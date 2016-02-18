/**
 * @file SortInference.hpp
 * Defines class SortInference.
 *
 *
 * NOTE: An important convention to remember is that when we have a DArray representing
 *       the signature or grounding of a function the lastt argument is the return
 *       so array[arity] is return and array[i] is the ith argument of the function
 */

#ifndef __SortInference__
#define __SortInference__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Kernel/Signature.hpp"

namespace FMB {
using namespace Kernel;
using namespace Shell;
using namespace Lib;


struct SortedSignature{
    unsigned sorts;
    DArray<Stack<unsigned>> sortedConstants;
    DArray<Stack<unsigned>> sortedFunctions;

    // for f(x,y) = z this will store sort(z),sort(x),sort(y)
    DArray<DArray<unsigned>> functionSignatures;
    // for p(x,y) this will store sort(x),sort(y)
    DArray<DArray<unsigned>> predicateSignatures;

    // gives the maximum size of a sort
    DArray<unsigned> sortBounds;
    
    // the number of distinct sorts that might have different sizes
    unsigned distinctSorts;

    // for each distinct sort gives a sort that can be used for variable equalities that are otherwise unsorted
    // some of these will not be used, we could detect these cases... but it is not interesting
    DArray<unsigned> varEqSorts;

    // the distinct parents of sorts
    // has length sorts with contents from distinctSorts
    // invariant: all monotonic sorts will have parent 0, the first non-monotonic sort
    DArray<unsigned> parents;

    // Map the distinct sorts back to their vampire parents
    // A distinct sort may merge multipe vampire sorts (due to monotonicity)
    DHMap<unsigned,Stack<unsigned>*> distinctToVampire;
    // A vampire sort can only be mapped to more than one distinct sort under certain conditions i.e. when
    // 
    DHMap<unsigned,unsigned> vampireToDistinct;

    // has size distinctSorts
    // is 1 if that distinct sort is monotonic
    ZIArray<bool> monotonicSorts;
};

class SortInference {
public:
  CLASS_NAME(SortInference);
  USE_ALLOCATOR(SortInference);    
  
  SortInference(ClauseList* clauses,
                DArray<unsigned> del_f,
                DArray<unsigned> del_p,
                Stack<DHSet<unsigned>*> equiv_v_sorts) :
                _clauses(clauses), _del_f(del_f), _del_p(del_p),_equiv_v_sorts(equiv_v_sorts), _equiv_vs(env.sorts->sorts()){

                  _sig = new SortedSignature();
                  _print = env.options->showFMBsortInfo();

                  _ignoreInference = env.options->fmbSortInference() == Options::FMBSortInference::IGNORE;
                  _expandSubsorts = env.options->fmbSortInference() == Options::FMBSortInference::EXPAND;

                  _usingMonotonicity = true;
                  _collapsingMonotonicSorts = env.options->fmbCollapseMonotonicSorts() != Options::FMBMonotonicCollapse::OFF;
                  _assumeMonotonic = _collapsingMonotonicSorts && 
                                     env.options->fmbCollapseMonotonicSorts() != Options::FMBMonotonicCollapse::GROUP;

                  _distinctSorts=0;
                  _collapsed=0;
                }

   void doInference();                

   SortedSignature* getSignature(){ return _sig; } 

private:

   unsigned getDistinctSort(unsigned subsort, unsigned vampireSort);

  bool _print;
  bool _ignoreInference;
  bool _expandSubsorts;
  bool _usingMonotonicity;
  bool _collapsingMonotonicSorts;
  bool _assumeMonotonic;

  unsigned _distinctSorts;
  unsigned _collapsed;
  DHSet<unsigned> monotonicVampireSorts;
  ZIArray<unsigned> posEqualitiesOnPos;

  SortedSignature* _sig;
  ClauseList* _clauses;
  DArray<unsigned> _del_f;
  DArray<unsigned> _del_p;
  Stack<DHSet<unsigned>*> _equiv_v_sorts;
  IntUnionFind _equiv_vs;

};

}

#endif // __SortInference__
