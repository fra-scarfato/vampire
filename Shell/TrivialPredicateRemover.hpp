/**
 * @file TrivialPredicateRemover.hpp
 * Defines class TrivialPredicateRemover.
 */

#ifndef __TrivialPredicateRemover__
#define __TrivialPredicateRemover__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Set.hpp"



namespace Shell {

using namespace Kernel;

class TrivialPredicateRemover {
public:
  void apply(UnitList*& units);

private:
  void scan(UnitList* units);
  void count(Clause* cl, int add);

  /** Number of clauses in which predicate occurs only positively */
  DArray<int> _posOcc;
  /** Number of clauses in which predicate occurs only negatively */
  DArray<int> _negOcc;

  typedef Set<Clause*> ClauseSet;

  DArray<ClauseSet> _predClauses;

  Stack<unsigned> _reachedZeroes;

  ClauseSet _removed;
};

}

#endif // __TrivialPredicateRemover__