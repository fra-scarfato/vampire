/**
 * @file ClauseDisposer.hpp
 * Defines class ClauseDisposer.
 */

#ifndef __ClauseDisposer__
#define __ClauseDisposer__

#include "Forwards.hpp"

#include "SATClause.hpp"

namespace SAT {

class ClauseDisposer
{
public:
  typedef SATClause::ActivityType ActivityType;

  ClauseDisposer(TWLSolver& solver) : _solver(solver) {}

  /**
   * This is a point at which it is safe to remove learnt
   * clauses.
   */
  virtual void onRestart() {}
  /**
   * This is a point at which it is safe to remove learnt
   * clauses.
   */
  virtual void onSafeSpot() {}
  virtual void onNewInputClause(SATClause* cl) {}
  virtual void onConflict() {}
  virtual void onClauseInConflict(SATClause* cl) {}
protected:
  unsigned decisionLevel();
  unsigned varCnt() const;
  SATClauseStack& getLearntStack();
  DArray<SATClauseStack>& getWatchedStackArray();
  SATClause* getAssignmentPremise(unsigned var);

  void markAllRemovableUnkept();
  void removeUnkept();
  void keepMostActive(size_t numberOfKept, ActivityType minActivity);
  void keepBinary();

  TWLSolver& _solver;
};

/**
 * This class takes care of increasing clause activity, but doesn't
 * perform clause deletion
 */
class DecayingClauseDisposer : public ClauseDisposer
{
public:
  DecayingClauseDisposer(TWLSolver& solver, ActivityType decayFactor = 1.001f)
   : ClauseDisposer(solver), _decayFactor(decayFactor), _inc(1e-30f) {}

  virtual void onConflict();

  virtual void onClauseInConflict(SATClause* cl) {
    cl->activity()+=_inc;
  }
protected:
  ActivityType _decayFactor;
  ActivityType _inc;
};

class MinisatClauseDisposer : public DecayingClauseDisposer
{
public:
  MinisatClauseDisposer(TWLSolver& solver, ActivityType decayFactor = 1.001f)
   : DecayingClauseDisposer(solver, decayFactor), _phaseIdx(0), _phaseLen(100), _clauseCntAcc(0), _survivorCnt(0) {}

  virtual void onNewInputClause(SATClause* cl);
  virtual void onSafeSpot();
  virtual void onConflict();
protected:

  size_t _phaseIdx;
  size_t _phaseLen;

  unsigned _clauseCntAcc;
  size_t _survivorCnt;
};

class GrowingClauseDisposer : public DecayingClauseDisposer
{
public:
  GrowingClauseDisposer(TWLSolver& solver, ActivityType decayFactor = 1.001f)
   : DecayingClauseDisposer(solver, decayFactor), _phaseIdx(0), _phaseLen(100), _clauseCntAcc(0), _survivorCnt(0) {}

  virtual void onNewInputClause(SATClause* cl);
  virtual void onRestart();
  virtual void onConflict();
protected:

  size_t _phaseIdx;
  size_t _phaseLen;

  unsigned _clauseCntAcc;
  size_t _survivorCnt;
};

}

#endif // __ClauseDisposer__