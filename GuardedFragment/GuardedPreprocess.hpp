#include "Kernel/Unit.hpp"
#include "Forwards.hpp"
#include "Kernel/Formula.hpp"

namespace GuardedFragment {

using namespace Kernel;

class Property;
class Options;


class GuardedPreprocess 
{
public:
/** Initialise the preprocessor */
  explicit GuardedPreprocess(const Shell::Options& options)
  : _options(options)
  {}
  void preprocess(Problem& prb);
  void preprocess1(Problem& prb);
  void preprocess2(Problem& prb);
  void skolemise(Problem& prb);
  Formula* structUQ(Formula* formula, Problem& prb, Unit* u);
  Formula* generateNewFormula(Formula* formula, AtomicFormula* lit, SList* sorts, VList* vars);
  void clausify(Problem& prb);
  void computeVarDepth(Problem& prb);
  void computeVarDepth(Clause* cl);
  void computeVarDepth(Literal* lit);
  int computeVarDepth(TermList t);
  void naming(Problem& prb);

  /** Options used in the normalisation */
  const Shell::Options& _options;
}; // class Preprocess
}