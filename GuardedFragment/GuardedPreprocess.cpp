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
#include "Shell/Naming.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/CNF.hpp"

#include "GuardedPreprocess.hpp"
#include "Classifier.hpp"
#include "Lib/Environment.hpp"
#include "Shell/SimplifyFalseTrue.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/TermIterators.hpp"

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

  // /* ennf and flattening */
  // preprocess1(prb);
  // /* naming to solve the explosion in NNF 
  // * take formulas in ennf */
  // naming(prb);
  
  /*nnf, flattening and structural universal quantifier transformation*/
  preprocess2(prb);

  


  if (env.options->showPreprocessing()) {
     UnitList::Iterator uit(prb.units());
     while(uit.hasNext()) {
      Unit* u = uit.next();
      env.out() << "[PP] before skolemisation: " << u->toString() << std::endl;
    }
  }

  /* skolemisation*/
  skolemise(prb);

  if (env.options->showPreprocessing()) {
     UnitList::Iterator uit(prb.units());
     while(uit.hasNext()) {
      Unit* u = uit.next();
      env.out() << "[PP] before clausification: " << u->toString() << std::endl;
    }
  }

  /* clausification formulae*/
  clausify(prb);

  computeVarDepth(prb);

  if (env.options->showPreprocessing()) {
     UnitList::Iterator uit(prb.units());
     while(uit.hasNext()) {
      Unit* u = uit.next();
      env.out() << "[PP] final: " << u->toString() << std::endl;
    }
  }



}

void GuardedPreprocess::computeVarDepth(Clause* cl)
{
  auto literals = cl->getLiteralIterator();
  while (literals.hasNext()) {
    Literal* lit = literals.next();
    computeVarDepth(lit);

    if(env.options->showGuarded()) {
      env.out() << "[PP] vardepth: " << lit->getVarDepth() << " of " << lit->toString() << endl;
    }
  }
  
}

void GuardedPreprocess::preprocess1(Problem& prb)
{
  env.statistics->phase=Statistics::PREPROCESS_2;

  UnitList::DelIterator us(prb.units());
  while (us.hasNext()) {
    Unit* u = us.next();

    if (u->isClause()) {
	continue;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    FormulaUnit* fu0 = fu;

    fu = NNF::ennf(fu);
    fu = Flattening::flatten(fu);


    if (fu != fu0) {
      us.replace(fu);
    }
  }
}

void GuardedPreprocess::preprocess2(Problem& prb)
{
  UnitList::DelIterator us(prb.units());
  while (us.hasNext()) {
    Unit* u = us.next();

    if (u->isClause()) continue;

    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    FormulaUnit* fu0 = fu;

    fu = SimplifyFalseTrue::simplify(fu);
    fu = Flattening::flatten(fu);
    
    /* 1. transform FOF formula in NNF*/
    fu = NNF::nnf(fu);
    fu = Flattening::flatten(fu);
    
    if(fu != fu0){
      us.replace(fu);
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << fu->toString() << std::endl;
      }
      fu0 = fu;
    }
    
    /* 2. transform NNF to Struct ∀ transformation (FLATTEN RULES random)*/
    Formula* args = structUQ(fu->formula(), prb, u);
    fu = new FormulaUnit(args, FormulaTransformation(InferenceRule::FLATTEN, u));
    
    if(fu != fu0){
      us.replace(fu);
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "SUQ replacement: "<< fu->toString() << std::endl;
      }
    }
  }
}

void GuardedPreprocess::skolemise(Problem& prb)
{
  bool modified = false;

  UnitList::DelIterator uit(prb.units());
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if (u->isClause()) continue;
    
    /* 3. skolemise formulae*/
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    FormulaUnit* fu0 = fu;

    fu = Skolem::skolemise(fu, false);

    if(fu != fu0){
      uit.replace(fu);
    }
  }

  if (modified) {
    prb.invalidateProperty();
  }
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

void GuardedPreprocess::naming(Problem& prb)
{
  ASS(_options.naming());

  env.statistics->phase=Statistics::NAMING;
  UnitList::DelIterator us(prb.units());
  //TODO fix the below
  Naming naming(_options.naming(),false, prb.isHigherOrder()); // For now just force eprPreservingNaming to be false, should update Naming
  while (us.hasNext()) {
    Unit* u = us.next();
    if (u->isClause()) {
      continue;
    }
    UnitList* defs;
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    FormulaUnit* v = naming.apply(fu,defs);
    if (v != fu) {
      ASS(defs);
      us.insert(defs);
      us.replace(v);
    }
  }
  prb.invalidateProperty();
}

Formula* GuardedPreprocess::structUQ(Formula* formula, Problem& prb, Unit* u)
{
  switch (formula->connective())
  {
    case FORALL: {
      
      Formula *subformula = formula->qarg();
      Formula* s = structUQ(subformula, prb, u);

      if (subformula != s) formula = new QuantifiedFormula(FORALL, formula->vars(), formula->sorts(), s);

      /* in this case the only form is ![X]:(~a(X,Y) V A) with almost one free variable y. so apply directly the transformation without control */
      if (subformula->connective() == OR && VList::isNonEmpty(formula->freeVariables())) {
        FormulaVarIterator freeVars(formula); 
        Stack<TermList> args;
        SList* newFormulaSorts = SList::empty();
        VList* newFormulaVars = VList::empty();
        
        while (freeVars.hasNext()){
          auto var = freeVars.next();
          /* default sort */
          SList::push(AtomicSort::defaultSort(), newFormulaSorts);
          /* add to VList free variables for new universal quantified formula */
          VList::push(var, newFormulaVars);
          /* args contain free variables which will be fresh literal variables*/
          args.push(TermList(var, false));
        }
        /* create fresh literal */
        auto newPred = env.signature->addFreshPredicate(args.size(), "gf");
        Literal *freshLit = Literal::create(newPred, args.size(), true, false, args.begin());
        AtomicFormula* freshLitAtom = new AtomicFormula(freshLit);

        /* generate ![X,Y]:(~a(X,Y) | ~gf(Y) | A) from ![X]:(~a(X,Y) V A) 
        *  where gf(Y) is the fresh literal */
        Formula* newFormula = generateNewFormula(formula, freshLitAtom, newFormulaSorts, newFormulaVars);
        FormulaUnit* newUnit = new FormulaUnit(newFormula, FormulaTransformation(InferenceRule::FLATTEN, u));
        
        UnitList::push(newUnit, prb.units());

        if (env.options->showPreprocessing()) {
          env.beginOutput();
          env.out() << "SUQ adding: "<< newUnit->toString() << std::endl;
        }
        formula = freshLitAtom;
      }
      return formula;
    }
    case EXISTS: {
      
      Formula* f = structUQ(formula->qarg(), prb, u);
      return (f == formula->qarg()) ? formula : new QuantifiedFormula(EXISTS, formula->vars(), formula->sorts(), f);
    }
    case IFF:
    case IMP: {
      Formula* left = structUQ(formula->left(), prb, u);
      Formula* right = structUQ(formula->right(), prb, u);
      if (left != formula->left() || right != formula->right()){
        return new BinaryFormula(formula->connective(), left, right);
      }
      return formula;
    }
    case OR:
    case AND: {
      FormulaList* newArgs = 0;
      FormulaList::Iterator it(formula->args());
      while (it.hasNext()) {
        Formula* f = structUQ(it.next(), prb, u);
        FormulaList::push(f, newArgs);
      }
      return (formula->args() == newArgs) ? formula : new JunctionFormula(formula->connective(), newArgs);
    }
    case NOT: {
      Formula* f = structUQ(formula->uarg(), prb, u);
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

Formula* GuardedPreprocess::generateNewFormula(Formula* formula, AtomicFormula* freshLiteral, SList* sorts, VList* vars)
{
  /* create SList and VList for new universal quantifier formula*/
  SList* newSorts = SList::concat(formula->sorts(), sorts);
  VList* newVars = VList::concat(formula->vars(), vars);

  Formula* subformula = formula->qarg();
  FormulaList* newArgs = FormulaList::empty();
  
  /* add args of previous formula to new uq formula args (guard is included) */
  FormulaList::push(subformula, newArgs);
  Literal* negatedFreshLiteral = Literal::complementaryLiteral(freshLiteral->literal());
  /* add new */
  FormulaList::push(new AtomicFormula(negatedFreshLiteral), newArgs);
  Formula* newFormulaArgs = new JunctionFormula(OR, newArgs);

  return new QuantifiedFormula(FORALL, newVars, newSorts, newFormulaArgs);
}

void GuardedPreprocess::computeVarDepth(Problem& prb)
{
  UnitList::Iterator us(prb.units());
  while (us.hasNext()) {
    Unit* u = us.next();
    auto literals = u->asClause()->getLiteralIterator();
    while (literals.hasNext()) {
      Literal* lit = literals.next();
      computeVarDepth(lit);

      if(env.options->showGuarded()) {
        env.out() << "[PP] vardepth: " << lit->getVarDepth() << " of " << lit->toString() << endl;
      }
    }
  }
}

void GuardedPreprocess::computeVarDepth(Literal* literal)
{
  if (literal->ground()) {
    literal->setVarDepth(-1);
    return;
  }

  int varDepth, max = 0;
  
  SubtermIterator si(literal);
  while (si.hasNext()){
    varDepth = 0;
    auto term = si.next();
    if (term.isTerm()) {
      varDepth = 1 + computeVarDepth(term);
      max = (max < varDepth) ? varDepth : max;
    }
  }

  literal->setVarDepth(max);
}

int GuardedPreprocess::computeVarDepth(TermList t) 
{
  Term* term = t.term();
  int max = 0, varDepth;

  SubtermIterator si(term);
  while (si.hasNext()){
    varDepth = 0;
    auto termOrVar = si.next();
    if(termOrVar.isTerm()) {
      varDepth = 1 + computeVarDepth(termOrVar);
      max = (max < varDepth) ? varDepth : max;
    }
  }
  return max;
}

