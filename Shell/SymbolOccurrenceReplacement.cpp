#include "Kernel/Formula.hpp"

#include "SymbolOccurrenceReplacement.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

Term* SymbolOccurrenceReplacement::process(Term* term) {
  CALL("FOOLElimination::SymbolOccurrenceReplacement::process(Term*)");
  if (term->isSpecial()) {
    Term::SpecialTermData* sd = term->getSpecialData();
    switch (term->functor()) {
      case Term::SF_ITE:
        return Term::createITE(process(sd->getCondition()), process(*term->nthArgument(0)), process(*term->nthArgument(1)), sd->getSort());

        case Term::SF_LET:
          if (_isPredicate == (sd->getBinding().isTerm() && sd->getBinding().term()->isBoolean())) {
            // function symbols, defined inside $let are expected to be
            // disjoint and fresh symbols are expected to be fresh
            ASS_NEQ(sd->getFunctor(), _symbol);
            ASS_NEQ(sd->getFunctor(), _freshSymbol);
          }
          return Term::createLet(sd->getFunctor(), sd->getVariables(), process(sd->getBinding()), process(*term->nthArgument(0)), sd->getSort());

        case Term::SF_FORMULA:
          return Term::createFormula(process(sd->getFormula()));

#if VDEBUG
        default:
          ASSERTION_VIOLATION;
#endif
    }
  }

  bool renaming = !_isPredicate && (term->functor() == _symbol);

  Stack<TermList> arguments;

  if (renaming) {
    Formula::VarList::Iterator fvit(_freeVars);
    while (fvit.hasNext()) {
      unsigned var = (unsigned)fvit.next();
      arguments.push(TermList(var, false));
    }
  }

  Term::Iterator it(term);
  while (it.hasNext()) {
    arguments.push(process(it.next()));
  }

  if (renaming) {
    unsigned arity = term->arity() + _freeVars->length();
    return Term::create(_freshSymbol, arity, arguments.begin());
  } else {
    return Term::create(term, arguments.begin());
  }
}

TermList SymbolOccurrenceReplacement::process(TermList ts) {
  CALL("FOOLElimination::SymbolOccurrenceReplacement::process(TermList)");

  if (!ts.isTerm()) {
    return ts;
  }

  return TermList(process(ts.term()));
}

Formula* SymbolOccurrenceReplacement::process(Formula* formula) {
  CALL("FOOLElimination::SymbolOccurrenceReplacement::process(Formula*)");
  switch (formula->connective()) {
    case LITERAL: {
      Literal* literal = formula->literal();

      bool renaming = _isPredicate && (literal->functor() == _symbol);

      Stack<TermList> arguments;

      if (renaming) {
        Formula::VarList::Iterator fvit(_freeVars);
        while (fvit.hasNext()) {
          arguments.push(TermList((unsigned)fvit.next(), false));
        }
      }

      Term::Iterator lit(literal);
      while (lit.hasNext()) {
        arguments.push(process(lit.next()));
      }

      Literal* processedLiteral;
      if (renaming) {
        unsigned arity = literal->arity() + _freeVars->length();
        bool polarity = (bool)literal->polarity();
        bool commutative = (bool)literal->commutative();
        processedLiteral = Literal::create(_freshSymbol, arity, polarity, commutative, arguments.begin());
      } else {
        processedLiteral = Literal::create(literal, arguments.begin());
      }

      return new AtomicFormula(processedLiteral);
    }

    case AND:
    case OR:
      return new JunctionFormula(formula->connective(), process(formula->args()));

    case IMP:
    case IFF:
    case XOR:
      return new BinaryFormula(formula->connective(), process(formula->left()), process(formula->right()));

    case NOT:
      return new NegatedFormula(process(formula->uarg()));

    case FORALL:
    case EXISTS:
      return new QuantifiedFormula(formula->connective(), formula->vars(), formula->sorts(), process(formula->qarg()));

    case BOOL_TERM:
      return new BoolTermFormula(process(formula->getBooleanTerm()));

    case TRUE:
    case FALSE:
      return formula;

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
    }
}

FormulaList* SymbolOccurrenceReplacement::process(FormulaList* formulas) {
  CALL("FOOLElimination::SymbolOccurrenceReplacement::process(FormulaList*)");
  return FormulaList::isEmpty(formulas) ? formulas : new FormulaList(process(formulas->head()), process(formulas->tail()));
}