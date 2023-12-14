#include "Kernel/Unit.hpp"
#include "Kernel/Formula.hpp"

namespace GuardedFragment {

using namespace Kernel;

class Classifier {
public:
    static bool isInGuardedFragment(UnitList* ul);
    static bool isInGuardedFragment(Formula* formula);
    static bool isInGuardedFragment(Clause* clause);
    static bool containsAllVariablesOfClause(TermList terms, DHSet<unsigned> allVars);
    static Literal *findGuardForImp(Formula *formula);
    static Literal* findGuardForOR(Formula* formula);
    static bool isGuard(Literal *mayGuard, DHSet<unsigned> allVars);
    static bool isGuard(Literal *mayGuard, VList *sorts);
};

}