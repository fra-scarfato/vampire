/**
 * @file BFNT.hpp
 * Defines class BFNT used to implement the transformation of clauses into
 * the EPR form described by Baumgartner, Fuchs, de Nivelle and Tinelli.
 * @since 30/07/2011 Manchester
 */


#ifndef __BFNT__
#define __BFNT__

#include "Forwards.hpp"

#include "Lib/Map.hpp"
#include "Lib/Stack.hpp"

using namespace Kernel;

namespace Shell {

/**
 * Class BFNT for implementing the transformation of clauses into
 * the EPR form described by Baumgartner, Fuchs, de Nivelle and Tinelli.
 * @since 30/07/2011 Manchester
 */
class BFNT
{
public:
  BFNT();
  void apply(UnitList* units);
  UnitList* create(unsigned modelSize);
private:
  Clause* apply(Clause* cl);
  static Clause* resolveNegativeVariableEqualities(Clause* cl);

  /** equality proxy symbol signature number */
  unsigned _proxy;
  /** map from function symbols to new predicate symbols denoting these functions */
  Map<unsigned,unsigned> _preds;
  /** transformed flat EPR clauses */
  Stack<Clause*> _flat;
  /** constants $1, $2, ... created to denote domain elements */
  Stack<Term*> _constants;
};

};

#endif /* __BFNT__ */