/**
 * @file FormulaTransformer.hpp
 * Defines class FormulaTransformer.
 */

#ifndef __FormulaTransformer__
#define __FormulaTransformer__

#include "Forwards.hpp"

#include "Inference.hpp"
#include "Sorts.hpp"

namespace Kernel {

class FormulaTransformer {
public:
  /**
   * This function is to be called from outside of the class to
   * transform formulas.
   */
  virtual Formula* transform(Formula* f) { return apply(f); }

protected:
  FormulaTransformer() {}

  Formula* apply(Formula* f);

  virtual Formula* applyLiteral(Formula* f) { return f; }

  virtual Formula* applyAnd(Formula* f) { return applyJunction(f); }
  virtual Formula* applyOr(Formula* f) { return applyJunction(f); }

  /** This function is called by applyAnd() and applyOr()
   * in their default implementation. */
  virtual Formula* applyJunction(Formula* f);

  virtual Formula* applyNot(Formula* f);

  virtual Formula* applyImp(Formula* f) { return applyBinary(f); }
  virtual Formula* applyIff(Formula* f) { return applyBinary(f); }
  virtual Formula* applyXor(Formula* f) { return applyBinary(f); }

  /** This function is called by applyImp(), applyIff()
   * and applyXor() in their default implementation. */
  virtual Formula* applyBinary(Formula* f);

  virtual Formula* applyForAll(Formula* f) { return applyQuantified(f); }
  virtual Formula* applyExists(Formula* f) { return applyQuantified(f); }

  /** This function is called by applyForAll() and applyExists()
   * in their default implementation. */
  virtual Formula* applyQuantified(Formula* f);


  virtual Formula* applyTrueFalse(Formula* f) { return f; }
};

class PolarityAwareFormulaTransformer : protected FormulaTransformer {
public:
  ~PolarityAwareFormulaTransformer();

  virtual Formula* transform(Formula* f, int polarity=1);
protected:
  PolarityAwareFormulaTransformer();

  virtual Formula* applyNot(Formula* f);

  virtual Formula* applyImp(Formula* f);

  virtual Formula* applyBinary(Formula* f);

  int polarity() const { return _polarity; }

  unsigned getVarSort(unsigned var) const;

private:
  DHMap<unsigned,unsigned>* _varSorts;
  int _polarity;
};

class FormulaUnitTransformer
{
public:
  virtual ~FormulaUnitTransformer() {}

  virtual FormulaUnit* transform(FormulaUnit* unit) = 0;

  void transform(UnitList*& units);
};


class LocalFormulaUnitTransformer : public FormulaUnitTransformer
{
public:
  LocalFormulaUnitTransformer(Inference::Rule rule)
  : _rule(rule) {}

  using FormulaUnitTransformer::transform;

  virtual Formula* transform(Formula* f) = 0;

  virtual FormulaUnit* transform(FormulaUnit* unit);

private:
  Inference::Rule _rule;
};

template<class FT>
class FTFormulaUnitTransformer : public LocalFormulaUnitTransformer
{
public:
  FTFormulaUnitTransformer(Inference::Rule rule, FT& formulaTransformer)
  : LocalFormulaUnitTransformer(rule), _formulaTransformer(formulaTransformer) {}

  using LocalFormulaUnitTransformer::transform;

  virtual Formula* transform(Formula* f)
  {
    CALL("FTFormulaUnitTransformer::transform(Formula*)");
    return _formulaTransformer.transform(f);
  }

private:
  FT& _formulaTransformer;
};

}

#endif // __FormulaTransformer__