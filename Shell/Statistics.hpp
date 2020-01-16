
/*
 * File Statistics.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Statistics.hpp
 * Defines proof-search statistics
 *
 * @since 02/01/2008 Manchester
 */

#ifndef __Statistics__
#define __Statistics__

#include <ostream>

#include "Forwards.hpp"

#include "Lib/RCPtr.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Lib/Allocator.hpp"

//#include "Kernel/Assignment.hpp"
//#include "Kernel/Constraint.hpp"

extern const char* VERSION_STRING;

namespace Kernel {
  class Unit;
}

namespace Shell {

using namespace std;
using namespace Kernel;
using namespace Solving;

/**
 * Class Statistics
 * @since 02/01/2008 Manchester
 */
class Statistics
{
public:
  CLASS_NAME(Statistics);
  USE_ALLOCATOR(Statistics);

  Statistics();

  void print(ostream& out);
  void explainRefutationNotFound(ostream& out);

  // Input
  /** number of input clauses */
  unsigned inputClauses;
  /** number of input formulas */
  unsigned inputFormulas;
  /** has types */
  bool hasTypes;

  // Preprocessing
  /** number of formula names introduced during preprocessing */
  unsigned formulaNames;
  /** number of skolem functions (also predicates in FOOL) introduced during skolemization */
  unsigned skolemFunctions;
  /** number of initial clauses */
  unsigned initialClauses;
  /** number of inequality splittings performed */
  unsigned splitInequalities;
  /** number of pure predicates */
  unsigned purePredicates;
  /** number of trivial predicates */
  unsigned trivialPredicates;
  /** number of unused predicate definitions */
  unsigned unusedPredicateDefinitions;
  /** number of eliminated function definitions */
  unsigned functionDefinitions;
  /** number of formulas selected by SInE selector */
  unsigned selectedBySine;
  /** number of iterations before SInE reached fixpoint */
  unsigned sineIterations;
  /** number of detected blocked clauses */
  unsigned blockedClauses;

  //Generating inferences
  /** number of clauses generated by factoring*/
  unsigned factoring;
  /** number of clauses generated by binary resolution*/
  unsigned resolution;
  /** number of clauses generated by unit resulting resolution*/
  unsigned urResolution;
  /** number of clauses generated by constrained resolution */
  unsigned cResolution;
  /** number of clauses generated by forward superposition*/
  unsigned forwardSuperposition;
  /** number of clauses generated by backward superposition*/
  unsigned backwardSuperposition;
  /** number of clauses generated by self superposition*/
  unsigned cSelfSuperposition;
  /** number of clauses generated by forward superposition*/
  unsigned cForwardSuperposition;
  /** number of clauses generated by backward superposition*/
  unsigned cBackwardSuperposition;
  /** number of clauses generated by self superposition*/
  unsigned selfSuperposition;
  /** number of clauses generated by equality factoring*/
  unsigned equalityFactoring;
  /** number of clauses generated by equality resolution*/
  unsigned equalityResolution;
  /** number of clauses generated by forward extensionality resolution*/
  unsigned forwardExtensionalityResolution;
  /** number of clauses generated by backward extensionality resolution*/
  unsigned backwardExtensionalityResolution;
  /** number of theory inst simp **/
  unsigned theoryInstSimp;
  /** number of theoryInstSimp candidates **/
  unsigned theoryInstSimpCandidates;
  /** number of theoryInstSimp tautologies **/
  unsigned theoryInstSimpTautologies;
  /** number of theoryInstSimp solutions lost as we could not represent them **/
  unsigned theoryInstSimpLostSolution;
  /** number of induction applications **/
  unsigned induction;
  unsigned maxInductionDepth;
  unsigned inductionInProof;
  unsigned generalizedInduction;
  unsigned generalizedInductionInProof;

  // Simplifying inferences
  /** number of duplicate literals deleted */
  unsigned duplicateLiterals;
  /** number of literals s |= s deleted */
  unsigned trivialInequalities;
  /** number of forward subsumption resolutions */
  unsigned forwardSubsumptionResolution;
  /** number of backward subsumption resolutions */
  unsigned backwardSubsumptionResolution;
  /** number of forward demodulations */
  unsigned forwardDemodulations;
  /** number of forward demodulations into equational tautologies */
  unsigned forwardDemodulationsToEqTaut;
  /** number of backward demodulations */
  unsigned backwardDemodulations;
  /** number of backward demodulations into equational tautologies */
  unsigned backwardDemodulationsToEqTaut;
  /** number of forward literal rewrites */
  unsigned forwardLiteralRewrites;
  /** number of condensations */
  unsigned condensations;
  /** number of global subsumptions */
  unsigned globalSubsumption;
  /** number of evaluations */
  unsigned evaluations;
  /** number of interpreted simplifications */
  unsigned interpretedSimplifications;
  /** number of (proper) inner rewrites */
  unsigned innerRewrites;
  /** number of inner rewrites into equational tautologies */
  unsigned innerRewritesToEqTaut;
  /** number of equational tautologies discovered by CC */
  unsigned deepEquationalTautologies;

  // Deletion inferences
  /** number of tautologies A \/ ~A */
  unsigned simpleTautologies;
  /** number of equational tautologies s=s */
  unsigned equationalTautologies;
  /** number of forward subsumed clauses */
  unsigned forwardSubsumed;
  /** number of backward subsumed clauses */
  unsigned backwardSubsumed;

  /** statistics of term algebra rules */
  unsigned taDistinctnessSimplifications;
  unsigned taDistinctnessTautologyDeletions;
  unsigned taInjectivitySimplifications;
  unsigned taNegativeInjectivitySimplifications;
  unsigned taAcyclicityGeneratedDisequalities;

  // Saturation
  /** all clauses ever occurring in the unprocessed queue */
  unsigned generatedClauses;
  /** all passive clauses */
  unsigned passiveClauses;
  /** all active clauses */
  unsigned activeClauses;
  /** all extensionality clauses */
  unsigned extensionalityClauses;

  unsigned discardedNonRedundantClauses;

  unsigned inferencesBlockedForOrderingAftercheck;

  bool smtReturnedUnknown;
  bool smtDidNotEvaluate;

  unsigned inferencesSkippedDueToColors;

  /** passive clauses at the end of the saturation algorithm run */
  unsigned finalPassiveClauses;
  /** active clauses at the end of the saturation algorithm run */
  unsigned finalActiveClauses;
  /** extensionality clauses at the end of the saturation algorithm run */
  unsigned finalExtensionalityClauses;

  unsigned splitClauses;
  unsigned splitComponents;
  //TODO currently not set, set it?
  unsigned uniqueComponents;
  /** Number of clauses generated for the SAT solver */
  unsigned satClauses;
  /** Number of unit clauses generated for the SAT solver */
  unsigned unitSatClauses;
  /** Number of binary clauses generated for the SAT solver */
  unsigned binarySatClauses;
  /** Number of clauses learned by the SAT solver */
  unsigned learntSatClauses;
  /** Number of literals in clauses learned by the SAT solver */
  unsigned learntSatLiterals;

  unsigned satSplits;
  unsigned satSplitRefutations;

  unsigned smtFallbacks;

  /* the next three variables keep statistics for Vampire default sat solver*/
  unsigned satTWLClauseCount;
  unsigned satTWLVariablesCount;
  unsigned satTWLSATCalls;

  unsigned instGenGeneratedClauses;
  unsigned instGenRedundantClauses;
  unsigned instGenKeptClauses;
  unsigned instGenIterations;

  unsigned maxBFNTModelSize;

  /** Number of pure variables eliminated by SAT solver */
  unsigned satPureVarsEliminated;

#if GNUMP
  /**
   * added for the purpose of Bound propagation
   * @since 25.10.2012 Vienna
   * @author Ioan Dragan
   */
  
  // Input
  /** number of input constraints */
  unsigned inputConstraints;
  /** number of input variables */
  unsigned inputVariables;
  /** number of constraints after preprocessing */
  unsigned preprocessedConstraints;
  /** number of variables after preprocessing */
  unsigned preprocessedVariables;

  // Preprocessing
  /** number of variables that were equivalent to some other
   * variable and were eliminated */
  unsigned equivalentVariables;
  /** number of variables eliminated by equality propagation */
  unsigned equalityPropagationVariables;
  /** number of constraints affected by equality propagation */
  unsigned equalityPropagationConstraints;
  /** number of eliminated constant variables */
  unsigned constantVariables;
  /** number of constraints updated by constant propagation */
  unsigned updatedByConstantPropagation;
  /** number of subsumed constraints */
  unsigned subsumedConstraints;
  /** number of variables appearing either only positively or only
   * negatively */
  unsigned halfBoundingVariables;
  /** number of constraints deleted due to half-bounding variables */
  unsigned halfBoundingConstraints;
  /** number of variables appearing either only positively or only
   * negatively except for one constraint */
  unsigned almostHalfBoundingVariables;
  /** number of constraints removed or replaced due to almost half-bounding variables */
  unsigned almostHalfBoundingConstraints;
  /** number of variables that were eliminated by Fourier-Motzkin because the
   * elimination introduced allowed amount of clauses */
  unsigned fmRemovedVariables;
  /** number of constraints introduced by Fourier-Motzkin variable elimination
   * in preprocessing */
  unsigned preprocessingFMIntroduced;
  /** number of constraints removed by Fourier-Motzkin variable elimination
   * in preprocessing */
  unsigned preprocessingFMRemoved;

  // Solving
  /** number of decision points where the variable was picked by heuristics */
  unsigned freeDecisionPoints;
  /** number of decision points where the variable was predetermined */
  unsigned forcedDecisionPoints;
  /** maximal number of decision points at a moment*/
  DecisionLevel maxDecisionDepth;
  /** number of backtracks */
  unsigned backtracks;
  /** number of backtracks by more than one decision level */
  unsigned longBacktracks;
  /** number of propagated bounds */
  unsigned propagatedBounds;
  /** number of generated conflict clauses */
  unsigned conflictClauses;
  /** how many times the conservative assigment selector reused previous assignment */
  unsigned assignmentsReusedByConservative;
  /** number of selected conflict that were not the most recent conflicts available */
  unsigned nonRecentConflicts;
  /** number of collapsing clauses that we retained for bound propagation */
  unsigned retainedConstraints;

  //Number representation
  /** True if native numbers were used during computation */
  bool nativeUsed;
  /** True if precise numbers were used during computation */
  bool preciseUsed;
  /** Time (in ms) when we switched from native to precise numbers */
  unsigned switchToPreciseTimeInMs;

  /** refutation if @c terminationReason==REFUTATION */
  ConstraintRCPtr bpRefutation;
  /** satisfying assignment if @c terminationReason==SATISFIABLE */
  ScopedPtr<Assignment> satisfyingAssigment;

#endif //GNUMP
  
  /** termination reason */
  enum TerminationReason {
    /** refutation found */
    REFUTATION,
    /** SAT SATISFIABLE */
    SAT_SATISFIABLE, 
    /** satisfiability detected (saturated set built) */
    SATISFIABLE,
    /** sat solver Unsatisfiable */
    SAT_UNSATISFIABLE,
    /** saturation terminated but an incomplete strategy was used */
    REFUTATION_NOT_FOUND,
    /** inappropriate strategy **/
    INAPPROPRIATE, 
    /** unknown termination reason */
    UNKNOWN,
    /** time limit reached */
    TIME_LIMIT,
    /** memory limit reached */
    MEMORY_LIMIT,
    /** activation limit reached */
    ACTIVATION_LIMIT
  };
  /** termination reason */
  TerminationReason terminationReason;
  /** refutation, if any */
  Kernel::Unit* refutation;
  /** the saturated set of clauses, if any */
  Kernel::UnitList* saturatedSet;
  /** if problem is satisfiable and we obtained a model, contains its
   * representation; otherwise it is an empty string */
  vstring model;

  enum ExecutionPhase {
    /** Whatever happens before we start parsing the problem */
    INITIALIZATION,
    PARSING,
    /** Scanning for properties to be passed to preprocessing */
    PROPERTY_SCANNING,
    NORMALIZATION,
    SINE_SELECTION,
    INCLUDING_THEORY_AXIOMS,
    PREPROCESS_1,
    PREDIACTE_DEFINITION_MERGING,
    PREDICATE_DEFINITION_INLINING,
    UNUSED_PREDICATE_DEFINITION_REMOVAL,
    BLOCKED_CLAUSE_ELIMINATION,
    PREPROCESS_2,
    NEW_CNF,
    NAMING,
    PREPROCESS_3,
    CLAUSIFICATION,
    FUNCTION_DEFINITION_ELIMINATION,
    INEQUALITY_SPLITTING,
    EQUALITY_RESOLUTION_WITH_DELETION,
    EQUALITY_PROXY,
    GENERAL_SPLITTING,
    SATURATION,
    /** The actual run of the conflict resolution algorithm */
    SOLVING,
    /** The actual run of the SAT solver*/
    SAT_SOLVING,
    PREPROCESSING,
    /** Whatever happens after the saturation algorithm finishes */
    FINALIZATION,
    FMB_PREPROCESSING,
    FMB_CONSTRAINT_GEN,
    FMB_SOLVING,
    UNKNOWN_PHASE
  };

  ExecutionPhase phase;

private:
  static const char* phaseToString(ExecutionPhase p);
}; // class Statistics

}

#endif
