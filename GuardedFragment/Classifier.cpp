#include <iostream>

#include "Forwards.hpp"
#include "Shell/Options.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Clause.hpp"

#include "Classifier.hpp"

namespace GuardedFragment {

using namespace Kernel;
using namespace std;

bool Classifier::isInGuardedFragment(UnitList* ul){
    bool isGuarded;
    UnitList::Iterator it1(ul);

    while(it1.hasNext()){
        auto unit = it1.next();
        if(env.options->showGuarded()){
            env.beginOutput();
            env.out() << "Classifing: " << unit->toString() << endl;
            env.endOutput();
        }
        if (unit->isClause()){
            isGuarded = isInGuardedFragment(unit->asClause());
        } else {
            isGuarded = isInGuardedFragment(unit->getFormula());
        }
        if (!isGuarded){
            if(env.options->showGuarded()){
                env.beginOutput();
                env.out() << "Formula not in guarded fragment " << unit->toString() << endl;
                env.endOutput();
            }
            return false;
        }        
    }
    return true;
}

bool Classifier::isInGuardedFragment(Formula* formula)
{
    switch (formula->connective()){
        case FORALL: {
            //cout << formula->toString() << endl;
            /* reverse print with OR? bug?? */
            Formula *subformula = formula->qarg();
            //cout << subformula->toString() << endl;
            Literal *mayGuard;
            //only ![X,Y](a(X,Y) => A) or ![X,Y](~a | A | ...) are accepted
            if (subformula->connective() == IMP && subformula->left()->connective() == LITERAL)
            {
                mayGuard = subformula->left()->literal();
                return (mayGuard->isPositive() && isGuard(mayGuard, formula->vars())) ? isInGuardedFragment(subformula->right()) : false;
            } 
            else if (subformula->connective() == OR)
            {
                FormulaList::Iterator fl(subformula->args());
                bool guardFound = false;
                while (fl.hasNext() && !guardFound)
                {
                    Formula* f = fl.next();
                    if (f->connective() == LITERAL) 
                    {
                        mayGuard = f->literal();
                        if(mayGuard->isNegative() && isGuard(mayGuard, formula->vars())) guardFound = true;
                    }    
                }
                return (guardFound) ? isInGuardedFragment(subformula) : false;
            }
            return false;
        }
        case EXISTS: {
            //cout << formula->toString() << endl;
            /* reverse print with OR? bug?? */
            Formula *subformula = formula->qarg();
            //cout << subformula->toString() << endl;
            Literal *mayGuard;
            if (subformula->connective() == AND)
            {
                FormulaList::Iterator fl(subformula->args());
                bool guardFound = false;
                while (fl.hasNext() && !guardFound)
                {
                    Formula* f = fl.next();
                    if (f->connective() == LITERAL) 
                    {
                        mayGuard = f->literal();
                        if(mayGuard->isPositive() && isGuard(mayGuard, formula->vars())) guardFound = true;
                    }    
                }
                return (guardFound) ? isInGuardedFragment(subformula) : false;
            }
            
            return false;
        }
        case IFF:
        case IMP:
            if (isInGuardedFragment(formula->left())) return isInGuardedFragment(formula->right());
            return false;
        case OR:
        case AND: {
            FormulaList::Iterator it(formula->args());
            while (it.hasNext())
            {
                if (!isInGuardedFragment(it.next())) return false;              
            }
            return true;    
        }
        case NOT:
            return isInGuardedFragment(formula->uarg());
        case LITERAL:
        case TRUE:
        case FALSE:
        case BOOL_TERM:
            return true;
        default:
            return false;
    }
    return true;
}

bool Classifier::isInGuardedFragment(Clause* clause)
{
    if (clause->isGround()) return true;
    
    static DHSet<unsigned> allVars;
    bool checkGuard = false;

    auto literals = clause->getLiteralIterator();
    clause->collectVars(allVars);

    while (literals.hasNext())
    {
        Literal *lit = literals.next();
     
        /*negative literal ¬A in c that does not contain a
        non-ground, functional term, and that contains all variables of c*/
        if (lit->isNegative() && !checkGuard){
            /* non guard are inspected also from while below
            OPTIMIZE....*/
            checkGuard = isGuard(lit, allVars);
            if (checkGuard) continue;
        }
        
        SubtermIterator terms(lit);
        /* every non-ground, functional term in c contains all variables of c*/
        while (terms.hasNext())
        {
            auto term = terms.next();
            terms.right();
            /* iterate on all variable 
            *e.g. A(X,f(X,Y,Z))
            X---f(X,Y,Z)---X---Y---Z*/
            //Solve with right
            if (term.isTerm())
            {
                if(!containsAllVariablesOfClause(term, allVars)) return false;
            }  
        }   
    }
    return checkGuard;

}


bool Classifier::containsAllVariablesOfClause(TermList term, DHSet<unsigned> allVars)
{
    Term* tptr = term.term();
    bool foundVar = false;
    
    auto vars = allVars.iterator();
    while (vars.hasNext())
    {
        auto var = vars.next();
        foundVar = false;
        SubtermIterator si(tptr);
        while (si.hasNext() && !foundVar)
        {
            auto termOrVar = si.next();
            si.right();
            if (termOrVar.isTerm()) return containsAllVariablesOfClause(termOrVar, allVars);
            if (var == termOrVar.var()) foundVar = true;   
        }

        if(!foundVar) return false;
    }

    return true;
}


bool Classifier::isGuard(Literal* mayGuard, DHSet<unsigned> allVars)
{
    bool foundVariable = false;
    auto vars = allVars.iterator();
    auto ex = allVars.iterator();
    
    while (vars.hasNext())
    {
        SubtermIterator si(mayGuard);
        auto var = vars.next();
        foundVariable = false;
        while (si.hasNext() && !foundVariable)
        {
            auto guardVariable = si.next();
            /* guard should not contain functional term */
            if (guardVariable.isTerm()) return false;
            if (var == guardVariable.var()) foundVariable = true;    
        }
        if (!foundVariable) return false;
    }
    return true;
}

bool Classifier::isGuard(Literal* mayGuard, VList* sorts)
{
    bool checkVariable = false;
    VList::Iterator it(sorts);
    /* stack and remove element found?*/
    VariableIterator guardVariable(mayGuard);

    while (it.hasNext())
    {
        auto sort = it.next();
        checkVariable = false;
        while (guardVariable.hasNext() && !checkVariable)
        {
            auto var = guardVariable.next().var();
            if (var == sort) checkVariable = true;
        }
        if(!checkVariable) return false;
        guardVariable.reset(mayGuard);
    }
    
    return true; 
}
}

