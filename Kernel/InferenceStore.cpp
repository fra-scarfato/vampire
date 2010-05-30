/**
 * @file InferenceStore.cpp
 * Implements class InferenceStore.
 */

#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"

#include "Shell/LaTeX.hpp"
#include "Shell/Options.hpp"
#include "Shell/Parser.hpp"

#include "BDD.hpp"
#include "Clause.hpp"
#include "Formula.hpp"
#include "FormulaUnit.hpp"
#include "FormulaVarIterator.hpp"
#include "Inference.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "InferenceStore.hpp"

//TODO: when we delete clause, we should also delete all its records from the inference store

namespace Kernel
{

using namespace std;
using namespace Lib;
using namespace Shell;

void InferenceStore::FullInference::increasePremiseRefCounters()
{
  CALL("InferenceStore::FullInference::increasePremiseRefCounters");

  for(unsigned i=0;i<premCnt;i++) {
    premises[i].cl()->incRefCnt();
  }
}



InferenceStore::InferenceStore()
: _bdd(BDD::instance())
{
}


InferenceStore::UnitSpec InferenceStore::getClauseSpec(Clause* cl)
{
  return UnitSpec(cl, cl->prop());
}
InferenceStore::UnitSpec InferenceStore::getClauseSpec(Clause* cl, BDDNode* prop)
{
  return UnitSpec(cl, prop);
}

string InferenceStore::getUnitIdStr(UnitSpec cs)
{
  CALL("InferenceStore::getUnitIdStr");

  if(!cs.isClause()) {
    return Int::toString(cs.unit()->number());
  }
  string suffix=getClauseIdSuffix(cs);
  if(suffix=="") {
    return Int::toString(cs.cl()->number());
  }
  return Int::toString(cs.cl()->number())+"_"+suffix;
}

string InferenceStore::getClauseIdSuffix(UnitSpec cs)
{
  CALL("InferenceStore::getClauseIdSuffix");

  FullInference* finf;
  if(_data.find(cs,finf)) {
    if(!finf->csId) {
      finf->csId=_nextClIds.insert(cs.cl());
    }
    return Int::toString(finf->csId);
  } else {
    //only clause constant prop. part can miss their Kernel-inference.
    if(_bdd->isTrue(cs.prop())) {
      return "T";
    } else {
      ASS(_bdd->isFalse(cs.prop()));
      return "";
    }
  }
}

void InferenceStore::recordNonPropInference(Clause* cl)
{
  CALL("InferenceStore::recordNonPropInference/1");

  bool nonTrivialProp=!_bdd->isConstant(cl->prop());
  if(!nonTrivialProp) {
    Inference* cinf=cl->inference();
    Inference::Iterator it = cinf->iterator();
    while (cinf->hasNext(it)) {
      Clause* prem=static_cast<Clause*>(cinf->next(it));
      ASS(prem->isClause());
      if(!_bdd->isFalse(prem->prop())) {
        nonTrivialProp=true;
        break;
      }
    }
  }

  if(nonTrivialProp) {
    recordNonPropInference(cl, cl->inference());
  }


}

void InferenceStore::recordNonPropInference(Clause* cl, Inference* cinf)
{
  CALL("InferenceStore::recordNonPropInference/2");
  ASS(!_bdd->isTrue(cl->prop()));

  static Stack<Clause*> prems(8);
  prems.reset();

  Inference::Iterator it = cinf->iterator();
  while (cinf->hasNext(it)) {
    Clause* prem=static_cast<Clause*>(cinf->next(it));
    ASS(prem->isClause());
    prems.push(prem);
  }

  unsigned premCnt=prems.size();
  FullInference* finf=new (premCnt) FullInference(premCnt);
  for(unsigned i=0;i<premCnt;i++) {
    finf->premises[i]=getClauseSpec(prems[i]);
  }
  finf->rule=cinf->rule();
  finf->increasePremiseRefCounters();
  _data.set(getClauseSpec(cl), finf);
}

void InferenceStore::recordPropReduce(Clause* cl, BDDNode* oldProp, BDDNode* newProp)
{
  CALL("InferenceStore::recordPropReduce");

  if(_bdd->isTrue(cl->prop())) {
    return;
  }
  recordPropAlter(cl, oldProp, newProp, Inference::PROP_REDUCE);
}

void InferenceStore::recordPropAlter(Clause* cl, BDDNode* oldProp, BDDNode* newProp,
	Inference::Rule rule)
{
  CALL("InferenceStore::recordPropAlter");
  ASS(!_bdd->isTrue(newProp));

  FullInference* finf=new (1) FullInference(1);
  finf->premises[0]=getClauseSpec(cl, oldProp);
  finf->rule=rule;
  finf->increasePremiseRefCounters();

  _data.set(getClauseSpec(cl, newProp), finf);
}

void InferenceStore::recordMerge(Clause* cl, BDDNode* oldClProp, Clause* addedCl, BDDNode* resultProp)
{
  CALL("InferenceStore::recordMerge/4");
  ASS(!_bdd->isTrue(resultProp));

  FullInference* finf=new (2) FullInference(2);
  finf->premises[0]=getClauseSpec(cl, oldClProp);
  finf->premises[1]=getClauseSpec(addedCl);
  finf->rule=Inference::COMMON_NONPROP_MERGE;
  finf->increasePremiseRefCounters();

  _data.set(getClauseSpec(cl, resultProp), finf);
}

void InferenceStore::recordMerge(Clause* cl, BDDNode* oldProp, BDDNode* addedProp, BDDNode* resultProp)
{
  CALL("InferenceStore::recordMerge/4");
  ASS(!_bdd->isTrue(resultProp));

  FullInference* finf=new (2) FullInference(2);
  finf->premises[0]=getClauseSpec(cl, oldProp);
  finf->premises[1]=getClauseSpec(cl, addedProp);
  finf->rule=Inference::COMMON_NONPROP_MERGE;
  finf->increasePremiseRefCounters();

  _data.set(getClauseSpec(cl, resultProp), finf);
}


void InferenceStore::recordMerge(Clause* cl, BDDNode* oldClProp, UnitSpec* addedCls, int addedClsCnt,
	BDDNode* resultProp)
{
  CALL("InferenceStore::recordMerge/5");
  ASS(!_bdd->isTrue(resultProp));

  FullInference* finf=new (addedClsCnt+1) FullInference(addedClsCnt+1);
  for(int i=0;i<addedClsCnt;i++) {
    finf->premises[i]=addedCls[i];
  }
  finf->premises[addedClsCnt]=getClauseSpec(cl, oldClProp);
  finf->rule=Inference::COMMON_NONPROP_MERGE;
  finf->increasePremiseRefCounters();

  _data.set(getClauseSpec(cl, resultProp), finf);
}


void InferenceStore::recordSplitting(SplittingRecord* srec, unsigned premCnt, Clause** prems)
{
  CALL("InferenceStore::recordSplitting");
  ASS(!_bdd->isTrue(srec->result.prop()));

  FullInference* finf=new (premCnt) FullInference(premCnt);
  for(unsigned i=0;i<premCnt;i++) {
    finf->premises[i]=getClauseSpec(prems[i]);
  }

  finf->rule=Inference::SPLITTING;
  finf->increasePremiseRefCounters();

  _data.set(srec->result, finf);

  //There is no need to increase reference counters in splitting premises,
  //as they're stored in the variant index of Splitter object, so won't get
  //deleted.
  _splittingRecords.set(srec->result, srec);
}

/**
 * Called before a clause is destroyed
 *
 * Deletes all records for the clause @b cl that can be efficiently reached,
 * as the clause is being destroyed and there will be no further need of them.
 */
void InferenceStore::deleteClauseRecords(Clause* cl)
{
  if(!cl->prop()) {
    return;
  }
  UnitSpec cs=getClauseSpec(cl);
  if(_data.find(cs)) {
    _data.remove(cs);
  }
}

InferenceStore::UnitSpecIterator InferenceStore::getParents(UnitSpec us, Inference::Rule& rule)
{
  CALL("InferenceStore::getParents/2");

  if(us.isPropTautology()) {
    rule=Inference::TAUTOLOGY_INTRODUCTION;
    return VirtualIterator<InferenceStore::UnitSpec>::getEmpty();
  }
  if(us.isClause()) {
    FullInference* finf;
    if(_data.find(us, finf)) {
      rule=finf->rule;
      return pvi( PointerIterator<UnitSpec>(finf->premises, finf->premises+finf->premCnt) );
    }
  }
  Unit* u=us.unit();
  List<UnitSpec>* res=0;
  Inference* inf=u->inference();
  Inference::Iterator iit=inf->iterator();
  while(inf->hasNext(iit)) {
    Unit* premUnit=inf->next(iit);
    List<UnitSpec>::push(UnitSpec(premUnit, true), res);
  }
  rule=inf->rule();
  return pvi( List<UnitSpec>::DestructiveIterator(res) );
}

InferenceStore::UnitSpecIterator InferenceStore::getParents(UnitSpec us)
{
  CALL("InferenceStore::getParents/1");

  Inference::Rule aux;
  return getParents(us, aux);
}


string getQuantifiedStr(Unit* u)
{
  Set<unsigned> vars;
  string res;
  if(u->isClause()) {
    Clause* cl=static_cast<Clause*>(u);
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      TermVarIterator vit( (*cl)[i] );
      while(vit.hasNext()) {
	vars.insert(vit.next());
      }
    }
    res=cl->nonPropToString();
  } else {
    Formula* formula=static_cast<FormulaUnit*>(u)->formula();
    FormulaVarIterator fvit( formula );
    while(fvit.hasNext()) {
	vars.insert(fvit.next());
    }
    res=formula->toString();
  }
  if(!vars.numberOfElements()) {
    return res;
  }
  Set<unsigned>::Iterator vit(vars);
  string varStr;
  bool first=true;
  while(vit.hasNext()) {
    if(!first) {
	varStr+=",";
    }
    varStr+=string("X")+Int::toString(vit.next());
    first=false;
  }

  return "( ! ["+varStr+"] : ("+res+") )";
}

struct InferenceStore::ProofPrinter
{
  ProofPrinter(Unit* refutation, ostream& out, InferenceStore* is)
  : is(is), out(out), bdd(BDD::instance())
  {
    CALL("InferenceStore::ProofPrinter::ProofPrinter");

    outputAxiomNames=env.options->outputAxiomNames();

    UnitSpec us(refutation, false);
    outKernel.push(us);
    handledKernel.insert(us);
  }

  virtual ~ProofPrinter() {}

  virtual void handleSplitting(SplittingRecord* sr)
  {
    requestProofStep(sr->premise);
    UnitSpec cs=sr->result;
    Clause* cl=cs.cl();
    out << is->getUnitIdStr(cs) << ". "
	<< cl->nonPropToString();
    if(!bdd->isFalse(cs.prop())) {
      out <<" | "<<bdd->toString(cs.prop());
    }
    out << " ("<<cl->age()<<':'<<cl->weight()<<") ";

    out <<"["<<Inference::ruleName(Inference::SPLITTING)<<" "
      <<is->getUnitIdStr(sr->premise);

    Stack<pair<int,Clause*> >::Iterator compIt(sr->namedComps);
    while(compIt.hasNext()) {
      out<<","<<compIt.next().second->number()<<"_D";
    }
    out <<"]\n";

    Stack<pair<int,Clause*> >::Iterator compIt2(sr->namedComps);
    while(compIt2.hasNext()) {
      pair<int,Clause*> nrec=compIt2.next();
      out<<nrec.second->number()<<"_D. ";
      if(nrec.second->length()==1 && (*nrec.second)[0]->arity()==0) {
	out<<(*nrec.second)[0]->predicateName();
      } else {
	out<<getQuantifiedStr(nrec.second);
      }
      out<<" <=> ";
      if(nrec.first>0) {
	out<<bdd->getPropositionalPredicateName(nrec.first);
      }
      else {
        out<<"~"<<bdd->getPropositionalPredicateName(-nrec.first);
      }
      out<<" ["<<Inference::ruleName(Inference::SPLITTING_COMPONENT)<<"]\n";
    }
  }

  virtual bool hideProofStep(Inference::Rule rule)
  {
    return false;
  }

  void requestProofStep(UnitSpec prem)
  {
    if(!bdd->isTrue(prem.prop()) && !handledKernel.contains(prem)) {
      handledKernel.insert(prem);
      outKernel.push(prem);
    }
  }

  virtual void printStep(UnitSpec cs)
  {
    Inference::Rule rule;
    UnitSpecIterator parents=is->getParents(cs, rule);

    out << is->getUnitIdStr(cs) << ". ";
    if(cs.isClause()) {
      Clause* cl=cs.cl();
      out << cl->nonPropToString();
      if(!bdd->isFalse(cs.prop())) {
  	out << " | "<<bdd->toString(cs.prop());
      }
      if(cl->splits() && !cl->splits()->isEmpty()) {
        out << " {" << cl->splits()->toString() << "}";
      }
      out << " ("<<cl->age()<<':'<<cl->weight()<<") ";
    }
    else {
      ASS(bdd->isFalse(cs.prop()));
      FormulaUnit* fu=static_cast<FormulaUnit*>(cs.unit());
      out << fu->formula()->toString();
    }

    out <<"["<<Inference::ruleName(rule);

    if(outputAxiomNames && rule==Inference::INPUT) {
      ASS(!parents.hasNext()); //input clauses don't have parents
      string name;
      if(Parser::findAxiomName(cs.unit(), name)) {
	out << " " << name;
      }
    }

    bool first=true;
    while(parents.hasNext()) {
      UnitSpec prem=parents.next();
      out << (first ? ' ' : ',');
      out << is->getUnitIdStr(prem);
      first=false;
    }

    out << "]" << endl;

  }

  void handleStep(UnitSpec cs)
  {
    Inference::Rule rule;
    UnitSpecIterator parents=is->getParents(cs, rule);

    if(rule==Inference::SPLITTING && is->_splittingRecords.find(cs)) {
      handleSplitting(is->_splittingRecords.get(cs));
      return;
    }

    while(parents.hasNext()) {
      UnitSpec prem=parents.next();
      ASS(prem!=cs);
      requestProofStep(prem);
    }

    if(!hideProofStep(rule)) {
      printStep(cs);
    }
  }

  virtual void print()
  {
    CALL("InferenceStore::ProofPrinter::print");

    while(outKernel.isNonEmpty()) {
      UnitSpec cs=outKernel.pop();
      bdd->allowDefinitionOutput(false);
      handleStep(cs);
      bdd->allowDefinitionOutput(true);
    }
  }

  /** Clauses that have propositional part assigned are put here
   * to be output as an inference step */
  Stack<UnitSpec> outKernel;
  Set<UnitSpec> handledKernel;

  InferenceStore* is;
  ostream& out;
  BDD* bdd;

  bool outputAxiomNames;
};

struct InferenceStore::TPTPProofPrinter
: public InferenceStore::ProofPrinter
{
  TPTPProofPrinter(Unit* refutation, ostream& out, InferenceStore* is)
  : ProofPrinter(refutation, out, is) {}

  string getRole(Inference::Rule rule)
  {
    switch(rule) {
    case Inference::INPUT:
      return "axiom";
    case Inference::NEGATED_CONJECTURE:
      return "negated_conjecture";
    default:
      return "plain";
    }
  }

  void printStep(UnitSpec cs)
  {
    Inference::Rule rule;
    UnitSpecIterator parents=is->getParents(cs, rule);

    out << "fof("<<is->getUnitIdStr(cs)<<","<<getRole(rule)<<",("<<endl;

    //print the unit itself

    out << "  "; //indent
    if(cs.isClause()) {
      Clause* cl=cs.cl();
      out << cl->nonPropToString();
      if(!bdd->isFalse(cs.prop())) {
  	out << " | "<<bdd->toString(cs.prop());
      }
      if(cl->splits() && !cl->splits()->isEmpty()) {
        out << " {" << cl->splits()->toString() << "}";
      }
      out << " ("<<cl->age()<<':'<<cl->weight()<<") ";
    }
    else {
      ASS(bdd->isFalse(cs.prop()));
      FormulaUnit* fu=static_cast<FormulaUnit*>(cs.unit());
      out << fu->formula()->toString();
    }

    out << "),"<<endl;

    //print inference

    out << "  "; //indent
    if(rule==Inference::INPUT || rule==Inference::NEGATED_CONJECTURE) {
      string fileName=env.options->inputFile();
      if(fileName.size()==0) {
	fileName="unknown";
      }
      string axiomName;
      if(!outputAxiomNames && !Parser::findAxiomName(cs.unit(), axiomName)) {
	axiomName="unknown";
      }
      out<<"file("<<fileName<<","<<axiomName<<")";
    }
    else {
      out <<"["<<Inference::ruleName(rule);

      bool first=true;
      while(parents.hasNext()) {
        UnitSpec prem=parents.next();
        out << (first ? ' ' : ',');
        out << is->getUnitIdStr(prem);
        first=false;
      }

      out << "]" << endl;
    }

    out << ")." << endl;

  }


};

struct InferenceStore::ProofCheckPrinter
: public InferenceStore::ProofPrinter
{
  ProofCheckPrinter(Unit* refutation, ostream& out, InferenceStore* is)
  : ProofPrinter(refutation, out, is) {}

  string bddToString(BDDNode* node)
  {
    return bdd->toTPTPString(node, "bddPred");
  }

  void printStep(UnitSpec cs)
  {
    Inference::Rule rule;
    UnitSpecIterator parents=is->getParents(cs, rule);

    out << "fof(r"<<is->getUnitIdStr(cs)
    	<< ",conjecture, "
    	<< getQuantifiedStr(cs.unit()) <<" | "<<bddToString(cs.prop())
    	<< " ). %"<<Inference::ruleName(rule)<<"\n";

    while(parents.hasNext()) {
      UnitSpec prem=parents.next();
      out << "fof(pr"<<is->getUnitIdStr(prem)
  	<< ",axiom, "
  	<< getQuantifiedStr(prem.unit());
      if(!bdd->isFalse(prem.prop())) {
	out << " | "<<bddToString(prem.prop());
      }
      out << " ).\n";
    }
    out << "%#\n";
  }

  virtual void printSplitting(SplittingRecord* sr)
  {
    requestProofStep(sr->premise);

    UnitSpec cs=sr->result;
    Clause* cl=cs.cl();

    out << "fof(r"<<is->getUnitIdStr(cs)
    	<< ",conjecture, "
    	<< getQuantifiedStr(cl) <<" | "<<bddToString(cs.prop())
    	<< " ). %"<<Inference::ruleName(Inference::SPLITTING)<<"\n";

    out << "fof(pr"<<is->getUnitIdStr(sr->premise)
    	<< ",axiom, "
    	<< getQuantifiedStr(sr->premise.cl()) <<" | "<<bddToString(sr->premise.prop())
    	<< " ).\n";

    Stack<pair<int,Clause*> >::Iterator compIt(sr->namedComps);
    while(compIt.hasNext()) {
      pair<int,Clause*> nrec=compIt.next();

      out << "fof(pr"<<nrec.second->number()<<"_D"
      << ",axiom, ";
      if(nrec.second->length()==1 && (*nrec.second)[0]->arity()==0) {
	out<<(*nrec.second)[0]->predicateName();
      } else {
	out<<getQuantifiedStr(nrec.second);
      }
      out << " <=> ";
      if(nrec.first<0) {
	out << "~";
      }
      out << "bddPred" << abs(nrec.first) << " ).\n";
    }
    out << "%#\n";
  }

  bool hideProofStep(Inference::Rule rule)
  {
    switch(rule) {
    case Inference::INPUT:
    case Inference::NEGATED_CONJECTURE:
    case Inference::CLAUSE_NAMING:
    case Inference::SPLITTING_COMPONENT:
    case Inference::INEQUALITY_SPLITTING_NAME_INTRODUCTION:
    case Inference::INEQUALITY_SPLITTING:
    case Inference::SKOLEMIZE:
    case Inference::EQUALITY_PROXY_REPLACEMENT:
    case Inference::EQUALITY_PROXY_AXIOM1:
    case Inference::EQUALITY_PROXY_AXIOM2:
    case Inference::BDDZATION:
      return true;
    default:
      return false;
    }
  }

  void print()
  {
    ProofPrinter::print();
    out << "%#\n";
  }
};



void InferenceStore::outputProof(ostream& out, Unit* refutation)
{
  CALL("InferenceStore::outputProof");

  switch(env.options->proof()) {
  case Options::PROOF_ON:
  {
    ProofPrinter pp(refutation, out, this);
    pp.print();
    return;
  }
  case Options::PROOF_PROOFCHECK:
  {
    ProofCheckPrinter pp(refutation, out, this);
    pp.print();
    return;
  }
  case Options::PROOF_TPTP:
  {
    NOT_IMPLEMENTED;
    TPTPProofPrinter pp(refutation, out, this);
    pp.print();
    return;
  }
  case Options::PROOF_OFF:
    return;
  }
}


InferenceStore* InferenceStore::instance()
{
  static InferenceStore* inst=0;
  if(!inst) {
    inst=new InferenceStore();
  }
  return inst;
}


}
