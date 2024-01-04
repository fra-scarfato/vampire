#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Indexing/LiteralIndex.hpp"

namespace GuardedFragment
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class GuardedResolution
: public Inferences::GeneratingInferenceEngine
{
public:
  CLASS_NAME(GuardedResolution);
  USE_ALLOCATOR(GuardedResolution);

  GuardedResolution() 
    : _index(0),
    _unificationWithAbstraction(false)
  {  }

  void attach(SaturationAlgorithm* salg);
  void detach();

  static Clause* generateClause(Clause* queryCl, Literal* queryLit, SLQueryResult res, const Shell::Options& opts, PassiveClauseContainer* passive=0, Ordering* ord=0, LiteralSelector* ls = 0);
  ClauseIterator generateClauses(Clause* premise);

private:
  struct UnificationsFn;
  struct ResultFn;

  BinaryResolutionIndex* _index;
  bool _unificationWithAbstraction;
};

};