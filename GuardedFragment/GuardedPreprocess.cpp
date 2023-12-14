#include "Lib/ScopedLet.hpp"
#include <iostream>

#include "Forwards.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/Flattening.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/CNF.hpp"

#include "GuardedPreprocess.hpp"
#include "Classifier.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Preprocess.hpp"
#include "Kernel/FormulaVarIterator.hpp"

using namespace Shell;
using namespace GuardedFragment;
using namespace Kernel;
using namespace std;

void GuardedPreprocess::preprocess(Problem& prb)
{
  if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "preprocessing started" << std::endl;
      UnitList::Iterator uit(prb.units());
      while(uit.hasNext()) {
        Unit* u = uit.next();
        env.out() << "[PP] input: " << u->toString() << std::endl;
    }
  }

  UnitList::DelIterator us(prb.units());
  while (us.hasNext()) {
    Unit* u = us.next();

    if (u->isClause()) continue;

    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    FormulaUnit* fu0 = fu;
    
    cout << fu->toString() << endl;
    
    /* 1. transform FOF formula in NNF*/
    fu = NNF::nnf(fu);
    fu = Flattening::flatten(fu);
    
    if(fu != fu0){
        us.replace(fu);
        cout << fu->toString() << endl;
        fu0 = fu;
    }

    /* 2. transform NNF to Struct ∀ transformation (FLATTEN RULES random)*/
    fu = new FormulaUnit(structUQ(fu->formula(), us), FormulaTransformation(InferenceRule::FLATTEN, u));

    if(fu != fu0){
        us.replace(fu);
        cout << fu->toString() << endl;
    }
    
    /* 3. skolemise formulae*/
    fu0 = fu;
    fu = Skolem::skolemise(fu, false);

    if(fu != fu0){
        us.replace(fu);
    }
  }

  /* 4. clausification formulae*/
  clausify(prb);

  if (env.options->showPreprocessing()) {
     UnitList::Iterator uit(prb.units());
     while(uit.hasNext()) {
      Unit* u = uit.next();
      env.out() << "[PP] final: " << u->toString() << std::endl;
    }
  }

}

Formula* GuardedPreprocess::structUQ(Formula* formula, UnitList::DelIterator us)
{
  switch (formula->connective())
  {
    case FORALL: {
      
      Formula *subformula = formula->qarg();
      Formula* s = structUQ(subformula, us);

      if (subformula != s) formula = new QuantifiedFormula(FORALL, formula->vars(), formula->sorts(), s);
      cout << subformula->toString() << endl;
      cout << formula->toString() << endl;

      /* in this case the only form is ![X]:(~a(X,Y) V A) with almost one free variable y. so apply directly the transformation without control */
      if (subformula->connective() == OR && VList::isNonEmpty(formula->freeVariables())) {
        FormulaVarIterator freeVars(formula); 
        Stack<TermList> args;
        SList* newFormulaSorts = SList::empty();
        VList* newFormulaVars = VList::empty();

        while (freeVars.hasNext()){
          auto var = freeVars.next();
          SList::push(TermList(var, false), newFormulaSorts);
          VList::push(var, newFormulaVars);
          args.push(TermList(var, false));
        }
        auto newPred = env.signature->addFreshPredicate(args.size(), "gf");
        Literal *freshLit = Literal::create(newPred, args.size(), true, false, args.begin());
        Formula* newFormula = generateNewFormula(formula, freshLit, newFormulaSorts, newFormulaVars);
        formula = new AtomicFormula(freshLit);
      }
      return formula;
    }
    case EXISTS: {
      
      Formula* f = structUQ(formula->qarg(), us);
      cout << f->toString() << endl;
      cout << formula->toString() << endl;
      return (f == formula->qarg()) ? formula : new QuantifiedFormula(EXISTS, formula->vars(), formula->sorts(), f);
    }
    case IFF:
    case IMP: {
      cout << formula->toString() << endl;
      Formula* left = structUQ(formula->left(), us);
      Formula* right = structUQ(formula->right(), us);
      cout << left->toString() << " , " << right->toString() << endl;
      if (left != formula->left() || right != formula->right()){
        return new BinaryFormula(formula->connective(), left, right);
      }
      return formula;
    }
    case OR:
    case AND: {
      cout << formula->toString() << endl;
      FormulaList* newArgs = 0;
      FormulaList::Iterator it(formula->args());
      while (it.hasNext()) {
        Formula* f = structUQ(it.next(), us);
        cout << f->toString() << endl;
        FormulaList::push(f, newArgs);
      }
      return (formula->args() == newArgs) ? formula : new JunctionFormula(formula->connective(), newArgs);
    }
    case NOT: {
      Formula* f = structUQ(formula->uarg(), us);
      cout << f->toString() << endl;
      cout << formula->toString() << endl;
      return (f == formula->uarg()) ? formula : new NegatedFormula(f);
    }  
    case LITERAL:
    case TRUE:
    case FALSE:
    case BOOL_TERM:
      return formula;  
    default:
      return formula;
        
  }
}

Formula* GuardedPreprocess::generateNewFormula(Formula* formula, Literal* lit, SList* sorts, VList* vars)
{
  SList* newSorts = SList::concat(formula->sorts(), sorts);
  VList* newVars = VList::concat(formula->vars(), vars);
  Formula* subformula = formula->qarg();
  Literal* mayGuard;
  FormulaList* newArgs = 0;
  AtomicFormula* guard = 0;
  
  FormulaList::Iterator fl(subformula->args());
  
  while (fl.hasNext())
  {
      Formula* f = fl.next();
      if (f->connective() == LITERAL) 
      {
          mayGuard = f->literal();
          // guard found
          if(mayGuard->isNegative() && Classifier::isGuard(mayGuard, formula->vars())) {
            guard = new AtomicFormula(mayGuard);
            
          }
      }    
  }
  
  FormulaList::push(guard, newArgs);
  FormulaList::push(new AtomicFormula(lit), newArgs);
  /*add other terms to newArgs*/
  Formula* newFormulaArgs = new JunctionFormula(OR, newArgs);
  return new QuantifiedFormula(FORALL, newVars, newSorts, newFormulaArgs);
}

void GuardedPreprocess::clausify(Problem& prb)
{
  env.statistics->phase=Statistics::CLAUSIFICATION;

  //we check if we haven't discovered an empty clause during preprocessing
  Unit* emptyClause = 0;

  bool modified = false;

  UnitList::DelIterator us(prb.units());
  CNF cnf;
  Stack<Clause*> clauses(32);
  while (us.hasNext()) {
    Unit* u = us.next();
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] clausify: " << u->toString() << std::endl;
      env.endOutput();
    }
    if (u->isClause()) {
      if (static_cast<Clause*>(u)->isEmpty()) {
        emptyClause = u;
        break;
      }
      continue;
    }
    modified = true;
    cnf.clausify(u,clauses);
    while (! clauses.isEmpty()) {
      Unit* u = clauses.pop();
      if (static_cast<Clause*>(u)->isEmpty()) {
        emptyClause = u;
        goto fin;
      }
      us.insert(u);
    }
    us.del();
  }
  fin:
  if (emptyClause) {
    UnitList::destroy(prb.units());
    prb.units() = 0;
    UnitList::push(emptyClause, prb.units());
  }
  if (modified) {
    prb.invalidateProperty();
  }
  prb.reportFormulasEliminated();
}