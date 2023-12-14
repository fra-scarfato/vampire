#include "Kernel/Unit.hpp"
#include "Forwards.hpp"

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
  Formula* structUQ(Formula* formula, UnitList::DelIterator us);
  Formula* generateNewFormula(Formula* formula, Literal* lit, SList* sorts, VList* vars);
  void clausify(Problem& prb);

  /** Options used in the normalisation */
  const Shell::Options& _options;
}; // class Preprocess
}