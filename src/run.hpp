/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2021, Jo Devriendt
Copyright (c) 2020-2021, Stephan Gocht
Copyright (c) 2014-2021, Jakob Nordström

Parts of the code were copied or adapted from MiniSat.

MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010  Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
***********************************************************************/

#pragma once

#include "Solver.hpp"
#include "typedefs.hpp"
#include "WeightedRandomSampling.h"
#include "random"

namespace rs {

namespace run {

extern Solver solver;

struct LazyVar
{
    Solver &solver;
    int coveredVars;
    int upperBound;
    Var currentVar;
    ID atLeastID = ID_Undef;
    ID atMostID = ID_Undef;
    ConstrSimple32 atLeast;  // X >= k + y1 + ... + yi
    ConstrSimple32 atMost;   // k + y1 + ... + yi-1 + (1+n-k-i)yi >= X

    LazyVar(Solver &slvr, const Ce32 cardCore, int cardUpperBound, Var startVar);

    ~LazyVar();

    void addVar(Var v, bool reified);

    ID addAtLeastConstraint(bool reified);

    ID addAtMostConstraint(bool reified);

    ID addSymBreakingConstraint(Var prevvar) const;

    ID addFinalAtMost(bool reified);

    int remainingVars() const;

    void setUpperBound(int cardUpperBound);
};

std::ostream& operator<<(std::ostream& o, const std::shared_ptr<LazyVar> lv);

template <typename SMALL>
struct LvM
{
    std::unique_ptr<LazyVar> lv;
    SMALL m;
};

struct DetailedLit
{
    long long coef_;
    Lit lit_;
    int consId_;

    DetailedLit()
    {
        coef_ = -1;
        lit_ = -1;
        consId_ = -1;
    }

    DetailedLit(long long coef, Lit l, int consId)
    {
        coef_ = coef;
        lit_ = l;
        consId_ = consId;
    }
};

template <typename SMALL, typename LARGE>
class Optimization
{
    const CePtr<ConstrExp<SMALL, LARGE>> origObj;
    CePtr<ConstrExp<SMALL, LARGE>> reformObj;

    LARGE lower_bound;
    LARGE upper_bound;
    ID lastUpperBound = ID_Undef;
    ID lastUpperBoundUnprocessed = ID_Undef;
    ID lastLowerBound = ID_Undef;
    ID lastLowerBoundUnprocessed = ID_Undef;

    std::vector<LvM<SMALL>> lazyVars;
    IntSet assumps;

    /***********************************************************************************************************************
    *                                          Assumption Guided Local Search                                              *
    ************************************************************************************************************************/
    int numConstr_;
    double softWeightSum_;
    double solutionImproveWeight_;
    std::vector<int> varCount_;
    std::vector<std::vector<DetailedLit>> varLit_;
    std::vector<double> satCount_;
    std::vector<double> satSlack_;
    std::vector<double> constrDegree_;
    std::vector<double> constrCoefSum_;
    std::vector<double> constrWeight_;
    std::vector<Var> orderedVarToCheck_;
    std::vector<Lit> greedyAssignment_;

    double objAvgCoef_;
    std::vector<double> constrAvgCoef_;

public:

Optimization(CePtr<ConstrExp<SMALL, LARGE>> obj) : origObj(obj)
{
    assert(origObj->vars.size() > 0);
    // NOTE: -origObj->getDegree() keeps track of the offset of the reformulated objective (or after removing unit lits)
    lower_bound = -origObj->getDegree();
    upper_bound = origObj->absCoeffSum() - origObj->getRhs() + 1;

    reformObj = solver.cePools.take<SMALL, LARGE>();
    reformObj->stopLogging();
    if (!options.optMode.is("linear")) {
        origObj->copyTo(reformObj);
    }
};

LARGE normalizedLowerBound() { return lower_bound + origObj->getDegree(); }
LARGE normalizedUpperBound() { return upper_bound + origObj->getDegree(); }

void printObjBounds()
{
    if (options.verbosity.get() == 0) return;
    std::cout << "c bounds ";
    if (solver.foundSolution()) {
        std::cout << bigint(upper_bound);  // TODO: remove bigint(...) hack
    } else {
        std::cout << "-";
    }
    std::cout << " >= " << bigint(lower_bound) << " @ " << stats.getTime() << "\n";  // TODO: remove bigint(...) hack
}

bool checkLazyVariables()
{
    bool reified = options.cgEncoding.is("reified");
    for (int i = 0; i < (int) lazyVars.size(); ++i) {
        LazyVar &lv = *lazyVars[i].lv;
        if (reformObj->getLit(lv.currentVar) == 0) {
            int cardCoreUpper = lv.upperBound;
            if (options.cgCoreUpper) {
                cardCoreUpper = static_cast<int>(std::min<LARGE>(cardCoreUpper,
                                                                 normalizedUpperBound() / lazyVars[i].m));
                // NOTE: integer division rounds down
            }
            assert(cardCoreUpper >= 0);
            lv.setUpperBound(cardCoreUpper);
            if (lv.remainingVars() == 0 ||
                isUnit(solver.getLevel(),
                       -lv.currentVar)) {  // binary constraints make all new auxiliary variables unit
                if (lv.addFinalAtMost(reified) == ID_Unsat) {
                    quit::exit_UNSAT(solver, upper_bound);
                    return true;
                }
                aux::swapErase(lazyVars, i--);  // fully expanded, no need to keep in memory
            } else {                          // add auxiliary variable
                long long newN = solver.getNbVars() + 1;
                solver.setNbVars(newN);
                Var oldvar = lv.currentVar;
                lv.addVar(newN, reified);
                // reformulate the objective
                reformObj->addLhs(lazyVars[i].m, newN);
                // add necessary lazy constraints
                if (lv.addAtLeastConstraint(reified) == ID_Unsat || lv.addAtMostConstraint(reified) == ID_Unsat ||
                    lv.addSymBreakingConstraint(oldvar) == ID_Unsat) {
                    quit::exit_UNSAT(solver, upper_bound);
                    return true;
                } else if (lv.remainingVars() == 0) {
                    aux::swapErase(lazyVars, i--);  // fully expanded, no need to keep in memory
                }
            }
        }
    }
    return false;
}

bool addLowerBound()
{
    CePtr<ConstrExp<SMALL, LARGE>> aux = solver.cePools.take<SMALL, LARGE>();
    origObj->copyTo(aux);
    aux->addRhs(lower_bound);
    solver.dropExternal(lastLowerBound, true, true);
    std::pair<ID, ID> res = solver.addConstraint(aux, Origin::LOWERBOUND);
    lastLowerBoundUnprocessed = res.first;
    lastLowerBound = res.second;
    if (lastLowerBound == ID_Unsat) {
        quit::exit_UNSAT(solver, upper_bound);
        return true;
    }
    return false;
}

std::pair<Ce32, int> reduceToCardinality(const CeSuper& core)
{
    int bestNbBlocksRemoved = 0;
    CeSuper card = core->clone(solver.cePools);
    if (options.cgReduction.is("clause")) {
        card->sortInDecreasingCoefOrder(
                [&](Var v1, Var v2) { return aux::abs(reformObj->coefs[v1]) > aux::abs(reformObj->coefs[v2]); });
        card->simplifyToClause();
    } else if (options.cgReduction.is("minslack")) {
        card->sortInDecreasingCoefOrder(
                [&](Var v1, Var v2) { return aux::abs(reformObj->coefs[v1]) > aux::abs(reformObj->coefs[v2]); });
        card->simplifyToMinLengthCardinality();
    } else {
        assert(options.cgReduction.is("bestbound"));
        CeSuper cloneCoefOrder = card->clone(solver.cePools);
        cloneCoefOrder->sortInDecreasingCoefOrder();
        std::reverse(cloneCoefOrder->vars.begin(), cloneCoefOrder->vars.end());  // *IN*creasing coef order
        card->sort([&](Var v1, Var v2) { return aux::abs(reformObj->coefs[v1]) > aux::abs(reformObj->coefs[v2]); });
        CeSuper clone = card->clone(solver.cePools);
        assert(clone->vars.size() > 0);
        LARGE bestLowerBound = 0;
        int bestNbVars = clone->vars.size();

        // find the optimum number of variables to weaken to
        int nbBlocksRemoved = 0;
        while (!clone->isTautology()) {
            int carddegree = cloneCoefOrder->getCardinalityDegreeWithZeroes();
            if (bestLowerBound < aux::abs(reformObj->coefs[clone->vars.back()]) * carddegree) {
                bestLowerBound = aux::abs(reformObj->coefs[clone->vars.back()]) * carddegree;
                bestNbVars = clone->vars.size();
                bestNbBlocksRemoved = nbBlocksRemoved;
            }
            SMALL currentObjCoef = aux::abs(reformObj->coefs[clone->vars.back()]);
            // weaken all lowest objective coefficient literals
            while (clone->vars.size() > 0 && currentObjCoef == aux::abs(reformObj->coefs[clone->vars.back()])) {
                ++nbBlocksRemoved;
                Var v = clone->vars.back();
                clone->weakenLast();
                cloneCoefOrder->weaken(v);
            }
        }

        // weaken to the optimum number of variables and generate cardinality constraint
        while ((int) card->vars.size() > bestNbVars) {
            card->weakenLast();
        }
        card->saturate();
        // sort in decreasing coef order to minimize number of auxiliary variables, but break ties so that *large*
        // objective coefficient literals are removed first, as the smallest objective coefficients are the ones that
        // will be eliminated from the objective function. Thanks Stephan!
        card->sortInDecreasingCoefOrder(
                [&](Var v1, Var v2) { return aux::abs(reformObj->coefs[v1]) < aux::abs(reformObj->coefs[v2]); });
        card->simplifyToCardinality(false);
    }

    Ce32 result = solver.cePools.take32();
    card->copyTo(result);
    return {result, bestNbBlocksRemoved};
}

bool handleInconsistency(std::vector<CeSuper>& cores)
{
    // take care of derived unit lits
    for (Var v: reformObj->vars) {
        if (isUnit(solver.getLevel(), v) || isUnit(solver.getLevel(), -v)) {
            assumps.remove(v);
            assumps.remove(-v);
        }
    }
    reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), false);
    [[maybe_unused]] LARGE prev_lower = lower_bound;
    lower_bound = -reformObj->getDegree();

    std::vector<std::pair<Ce32, int>> cardCores;
    for (CeSuper &core: cores) {
        assert(core);
        if (core->isTautology()) {
            continue;
        }
        if (core->hasNegativeSlack(solver.getLevel())) {
            assert(solver.decisionLevel() == 0);
            if (solver.logger) core->logInconsistency(solver.getLevel(), solver.getPos(), stats);
            quit::exit_UNSAT(solver, upper_bound);
            return true;
        }
        // figure out an appropriate core
        cardCores.push_back(reduceToCardinality(core));
    }

    if (cardCores.size() == 0) {
        // only violated unit assumptions were derived
        ++stats.UNITCORES;
        assert(lower_bound > prev_lower);
        if (checkLazyVariables()) return true;
        if (addLowerBound()) return true;
        if (!options.cgIndCores) assumps.clear();
        return false;
    }

    stats.SINGLECORES += cardCores.size() == 1;

    LARGE bestLowerBound = -1;
    Ce32 &bestCardCore = cardCores[0].first;
    int bestBlocksRemoved = 0;
    for (int i = 0; i < (int) cardCores.size(); ++i) {
        Ce32 cardCore = cardCores[i].first;
        assert(cardCore->hasNoZeroes());
        assert(cardCore->vars.size() > 0);
        SMALL lowestCoef = aux::abs(reformObj->coefs[cardCore->vars[0]]);
        for (Var v: cardCore->vars) {
            if (aux::abs(reformObj->coefs[v]) < lowestCoef) lowestCoef = aux::abs(reformObj->coefs[v]);
        }
        LARGE lowerBound = lowestCoef * cardCore->degree;
        if (i == 1) {
            stats.NOCOREBEST += lowerBound == bestLowerBound;
            stats.FIRSTCOREBEST += lowerBound < bestLowerBound;
            stats.DECCOREBEST += lowerBound > bestLowerBound;
        }
        if (lowerBound > bestLowerBound) {
            bestLowerBound = lowerBound;
            bestCardCore = cardCore;
            bestBlocksRemoved = cardCores[i].second;
        }
    }

    stats.REMOVEDBLOCKS += bestBlocksRemoved;
    stats.NCORECARDINALITIES += !bestCardCore->isClause();
    stats.COREDEGSUM += bestCardCore->getDegree();
    stats.CORESLACKSUM += bestCardCore->vars.size() - bestCardCore->getDegree();

    for (Var v: bestCardCore->vars) {
        assert(assumps.has(-bestCardCore->getLit(v)));
        assumps.remove(-bestCardCore->getLit(v));  // independent cores
    }

    // adjust the lower bound
    SMALL mult = 0;
    for (Var v: bestCardCore->vars) {
        assert(reformObj->getLit(v) != 0);
        if (mult == 0) {
            mult = aux::abs(reformObj->coefs[v]);
        } else if (mult == 1) {
            break;
        } else {
            mult = std::min(mult, aux::abs(reformObj->coefs[v]));
        }
    }
    assert(mult > 0);
    lower_bound += bestCardCore->getDegree() * mult;

    int cardCoreUpper = bestCardCore->vars.size();
    if (options.cgCoreUpper) {
        cardCoreUpper = static_cast<int>(std::min<LARGE>(cardCoreUpper, normalizedUpperBound() / mult));
        // NOTE: integer division rounds down
    }
    assert(cardCoreUpper >= 0);

    if (options.cgEncoding.is("sum") || bestCardCore->vars.size() - bestCardCore->getDegree() <= 1) {
        // add auxiliary variables
        long long oldN = solver.getNbVars();
        long long newN = oldN - static_cast<int>(bestCardCore->getDegree()) + cardCoreUpper;
        solver.setNbVars(newN);
        // reformulate the objective
        for (Var v = oldN + 1; v <= newN; ++v) bestCardCore->addLhs(-1, v);
        bestCardCore->invert();
        reformObj->addUp(bestCardCore, mult);
        assert(lower_bound == -reformObj->getDegree());
        // add channeling constraints
        if (solver.addConstraint(bestCardCore, Origin::COREGUIDED).second == ID_Unsat) {
            quit::exit_UNSAT(solver, upper_bound);
            return true;
        }
        bestCardCore->invert();
        if (solver.addConstraint(bestCardCore, Origin::COREGUIDED).second == ID_Unsat) {
            quit::exit_UNSAT(solver, upper_bound);
            return true;
        }
        for (Var v = oldN + 1; v < newN; ++v) {  // add symmetry breaking constraints
            if (solver.addConstraint(ConstrSimple32({{1, v},
                                                     {1, -v - 1}}, 1), Origin::COREGUIDED).second == ID_Unsat) {
                quit::exit_UNSAT(solver, upper_bound);
                return true;
            }
        }
    } else {
        bool reified = options.cgEncoding.is("reified");
        // add auxiliary variable
        long long newN = solver.getNbVars() + 1;
        solver.setNbVars(newN);
        // reformulate the objective
        bestCardCore->invert();
        reformObj->addUp(bestCardCore, mult);
        bestCardCore->invert();
        reformObj->addLhs(mult, newN);  // add only one variable for now
        assert(lower_bound == -reformObj->getDegree());
        // add first lazy constraint
        lazyVars.push_back({std::make_unique<LazyVar>(solver, bestCardCore, cardCoreUpper, newN), mult});
        lazyVars.back().lv->addAtLeastConstraint(reified);
        lazyVars.back().lv->addAtMostConstraint(reified);
    }
    if (checkLazyVariables()) return true;
    if (addLowerBound()) return true;
    if (!options.cgIndCores) assumps.clear();
    return false;
}

bool handleNewSolution(const std::vector<Lit>& sol)
{
    [[maybe_unused]] LARGE prev_val = upper_bound;
    upper_bound = -origObj->getRhs();
    for (Var v: origObj->vars) upper_bound += origObj->coefs[v] * (int) (sol[v] > 0);
    normalized_upperbound = (bigint)upper_bound + obj_offset;
    assert(upper_bound < prev_val);

    CePtr<ConstrExp<SMALL, LARGE>> aux = solver.cePools.take<SMALL, LARGE>();
    origObj->copyTo(aux);
    aux->invert();
    aux->addRhs(-upper_bound + 1);
    solver.dropExternal(lastUpperBound, true, true);
    std::pair<ID, ID> res = solver.addConstraint(aux, Origin::UPPERBOUND);
    lastUpperBoundUnprocessed = res.first;
    lastUpperBound = res.second;
    if (lastUpperBound == ID_Unsat) {
        quit::exit_UNSAT(solver, upper_bound);
        return true;
    }
    return false;
}

void logProof()
{
    if (!solver.logger) return;
    assert(lastUpperBound != ID_Undef);
    assert(lastUpperBound != ID_Unsat);
    assert(lastLowerBound != ID_Undef);
    assert(lastLowerBound != ID_Unsat);
    CePtr<ConstrExp<SMALL, LARGE>> coreAggregate = solver.cePools.take<SMALL, LARGE>();
    CePtr<ConstrExp<SMALL, LARGE>> aux = solver.cePools.take<SMALL, LARGE>();
    origObj->copyTo(aux);
    aux->invert();
    aux->addRhs(1 - upper_bound);
    aux->resetBuffer(lastUpperBoundUnprocessed);
    coreAggregate->addUp(aux);
    aux->reset();
    origObj->copyTo(aux);
    aux->addRhs(lower_bound);
    aux->resetBuffer(lastLowerBoundUnprocessed);
    coreAggregate->addUp(aux);
    assert(coreAggregate->hasNegativeSlack(solver.getLevel()));
    assert(solver.decisionLevel() == 0);
    coreAggregate->logInconsistency(solver.getLevel(), solver.getPos(), stats);
}

bool harden()
{
    LARGE diff = upper_bound - lower_bound;
    for (Var v: reformObj->vars) {
        if (aux::abs(reformObj->coefs[v]) > diff &&
            solver.addUnitConstraint(-reformObj->getLit(v), Origin::HARDENEDBOUND).second == ID_Unsat) {
            quit::exit_UNSAT(solver, upper_bound);
            return true;
        }
    }
    return false;
}

void optimize()
{
    size_t upper_time = 0, lower_time = 0;
    SolveState reply = SolveState::SAT;
    SMALL coeflim = options.cgStrat ? reformObj->getLargestCoef() : 0;

    enum class CoefLimStatus {
        START, ENCOUNTEREDSAT, REFINE
    };
    CoefLimStatus coefLimFlag = CoefLimStatus::REFINE;
    while (true) {
        size_t current_time = stats.getDetTime();
        if (options.time_limit.get() != -1.0 && stats.getTime() > options.time_limit.get()) {
            std::cout << "time limit reached\n";
            return;
        }
        if (reply != SolveState::INPROCESSED && reply != SolveState::RESTARTED) printObjBounds();

        // NOTE: only if assumptions are empty will they be refilled
        if (assumps.isEmpty() &&
            (options.optMode.is("coreguided") ||
             (options.optMode.is("coreboosted") && stats.getRunTime() < options.cgBoosted.get()) ||
             (options.optMode.is("hybrid") &&
              lower_time <
              options.cgHybrid.get() * (upper_time + lower_time)))) {  // use core-guided step by setting assumptions
            reformObj->removeZeroes();
            if (coeflim > 0 && coefLimFlag == CoefLimStatus::REFINE) {
                // find a new coeflim
                reformObj->sortInDecreasingCoefOrder();
                int numLargerCoefs = 0;
                int numLargerUniqueCoefs = 0;
                SMALL prevCoef = -1;
                bool changed = false;
                for (Var v: reformObj->vars) {
                    SMALL coef = aux::abs(reformObj->coefs[v]);
                    ++numLargerCoefs;
                    numLargerUniqueCoefs += prevCoef != coef;
                    prevCoef = coef;
                    if (coeflim > coef && numLargerCoefs / numLargerUniqueCoefs > 1.25) {
                        changed = true;
                        coeflim = coef;
                        break;
                    }
                }
                if (!changed) {
                    coeflim = 0;
                }
            }
            std::vector<Term<double>> litcoefs;  // using double will lead to faster sort than bigint
            litcoefs.reserve(reformObj->vars.size());
            for (Var v: reformObj->vars) {
                assert(reformObj->getLit(v) != 0);
                SMALL cf = aux::abs(reformObj->coefs[v]);
                if (cf >= coeflim) litcoefs.emplace_back(static_cast<double>(cf), v);
            }
            std::sort(litcoefs.begin(), litcoefs.end(), [](const Term<double> &t1, const Term<double> &t2) {
                return t1.c > t2.c || (t1.l < t2.l && t1.c == t2.c);
            });
            for (const Term<double> &t: litcoefs) assumps.add(-reformObj->getLit(t.l));
            coefLimFlag = CoefLimStatus::ENCOUNTEREDSAT;
        }
        assert(upper_bound > lower_bound);
         std::cout << "c nAssumptions for solve: " << assumps.size() << " @ " << stats.getTime() << " s\n";
        SolveAnswer out = aux::timeCall<SolveAnswer>(
                [&] {
                    solver.setAssumptions(assumps);
                    return solver.solve();
                },
                assumps.isEmpty() ? stats.SOLVETIME : stats.SOLVETIMECG);
        reply = out.state;
        if (reply == SolveState::RESTARTED) continue;
        if (reply == SolveState::UNSAT) {
            printObjBounds();
            quit::exit_UNSAT(solver, upper_bound);
            return;
        }
        if (assumps.isEmpty()) {
            upper_time += stats.getDetTime() - current_time;
        } else {
            lower_time += stats.getDetTime() - current_time;
        }
        if (reply == SolveState::SAT) {
            assumps.clear();
            assert(solver.foundSolution());
            ++stats.NSOLS;
            if (handleNewSolution(out.solution)) return;
            if (harden()) return;
            if (coefLimFlag == CoefLimStatus::ENCOUNTEREDSAT) coefLimFlag = CoefLimStatus::REFINE;
        } else if (reply == SolveState::INCONSISTENT) {
            assert(!options.optMode.is("linear"));
            ++stats.NCORES;
            if (handleInconsistency(out.cores)) return;
            if (harden()) return;
            coefLimFlag = CoefLimStatus::START;
        } else {
            assert(reply == SolveState::INPROCESSED);  // keep looping
            // coefLimFlag = CoefLimStatus::REFINE;
            // NOTE: above avoids long non-terminating solve calls due to insufficient assumptions
            assumps.clear();
        }
        if (lower_bound >= upper_bound) {
            printObjBounds();
            logProof();
            quit::exit_UNSAT(solver, upper_bound);
            return;
        }
    }
}

/***********************************************************************************************************************
*                                          Assumption Guided Local Search                                              *
************************************************************************************************************************/

enum struct Arm { Greedy, Exploit, Empty };

struct SearchStateInformation
{
    SolveState state_;                                                       // search state
    int restartBudget_;                                                      // restart budget for CDCL solving
    size_t numFails_, numInconsistencies_, numSolutions_;                    // search state counts
    std::vector<Lit> incumbentSolu_;                                         // solutions
    std::vector<CeSuper> cores_;                                             // inconsistent cores
    double averageObjCoefficient_;

    Arm arm_ = Arm::Greedy;
    double totalConflicts_;
    double greedyRewards_, exploitRewards_, emptyRewards_;
    double greedyConflicts_, exploitConflicts_, emptyConflicts_;

    SearchStateInformation()
    {
        state_ = SolveState::RESTARTED;
        restartBudget_ = options.aglsRestartsBudget.get();
        numFails_ = 0, numInconsistencies_ = 0, numSolutions_ = 0;
        incumbentSolu_ = {};
        cores_ = {};

        totalConflicts_ = 1;
        greedyRewards_ = 0, exploitRewards_ = 0, emptyRewards_ = 0;
        greedyConflicts_ = 0, exploitConflicts_ = 0, emptyConflicts_ = 0;
        averageObjCoefficient_ = 0;
    }
};

void AssumptionGuidedLocalSearch()
{
    // set random seed
    srand(options.aglsRandomSeed.get());

    // search state information
    SearchStateInformation ssi;

    // initialize
    InitializeSearch(ssi);

    // main loop
    while (stats.getRunTime() < options.time_limit.get()) {
        // update stats
        ++stats.NumLoops;

        // set assumption
        PickAssumption(ssi);

        // call CDCL solver
        Solve(ssi);

        // post process
        if (ssi.state_ == SolveState::SAT) {
            // new solution found
            UpdateUpperbound(ssi);
        } else if (ssi.state_ == SolveState::UNSAT) {
            // infeasibility has been proved
            quit::exit_UNSAT(solver, upper_bound);
        } else if (ssi.state_ == SolveState::INPROCESSED) {
            // out of search budget
            ProcessExceedingConflictsBudget(ssi);
        }
    }
    quit::exit_INDETERMINATE(solver);
}

void InitializeSearch(SearchStateInformation& ssi)
{
    // initialize random-greedy assumption
    if (options.aglsAssumptionHeuristic.is("greedy")) {
        InitializeGreedyAssumption();
    }

    // clone origin objective to reformulate objective
    origObj->copyTo(reformObj);
    reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), false);
    reformObj->sortInDecreasingCoefOrder();

    // get initial solution and initialize the search state
    if (!GetInitialSolution(ssi)) {
        normalized_upperbound = origObj->absCoeffSum();
        return;
    } else {
        ++ssi.numSolutions_;
        ssi.incumbentSolu_ = solver.lastSol;
    }
}

bool GetInitialSolution(SearchStateInformation& ssi)
{
    // get initial solution
    if (options.aglsInitialSolutionHeuristic.is("mpi-cdcl")) {
        // find initial solution by CDCL solving
        GetInitSolutionByMPIHeuristic(ssi);
    } else if (options.aglsInitialSolutionHeuristic.is("greedy")) {
        // find initial solution by CDCL solving and improve it greedily
        GetInitSolutionByMPIHeuristic(ssi);
        GetInitSolutionByGreedyHeuristic(ssi);
    } else if (options.aglsInitialSolutionHeuristic.is("structure")) {
        // find initial solution by linear search with structure-score guided phase selection
        GetInitSolutionByMPIHeuristic(ssi);
        GetInitSolutionByStructureBasedPhase(ssi);
    } else if (options.aglsInitialSolutionHeuristic.is("hybrid")) {
        // find initial solution by sequence heuristic
        GetInitSolutionByHybridHeuristic(ssi);
    } else if (options.aglsInitialSolutionHeuristic.is("greedyPhase")) {
        // find initial solution by linear search with phase resetting
        GetInitSolutionByGreedyPhaseHeuristic(ssi);
    } else if (options.aglsInitialSolutionHeuristic.is("default")) {
        // find initial solution by linear search
        GetInitSolutionByDefaultHeuristic(ssi);
    }

    return solver.foundSolution();
}

void PickAssumption(SearchStateInformation& ssi)
{
    if (options.aglsChooseArm.is("all")) {
        // compute ucb value of each arm
        double ucbValueGreedy = ssi.greedyRewards_ + options.aglsAssumptionUcbFactor.get() *
                                                         sqrt(log(ssi.totalConflicts_) / (ssi.greedyConflicts_ + 1));
        double ucbValueExploit = ssi.exploitRewards_ + options.aglsAssumptionUcbFactor.get() *
                                                           sqrt(log(ssi.totalConflicts_) / (ssi.exploitConflicts_ + 1));
        double ucbValueEmpty = ssi.emptyRewards_ + options.aglsAssumptionUcbFactor.get() *
                                                       sqrt(log(ssi.totalConflicts_) / (ssi.emptyConflicts_ + 1));
        if (ucbValueEmpty > ucbValueGreedy && ucbValueEmpty > ucbValueExploit) {
            ssi.arm_ = Arm::Empty;
        } else if (ucbValueExploit > ucbValueGreedy) {
            ssi.arm_ = Arm::Exploit;
        } else {
            ssi.arm_ = Arm::Greedy;
        }
    } else if (options.aglsChooseArm.is("exploit")) {
        ssi.arm_ = Arm::Exploit;
    } else if (options.aglsChooseArm.is("greedy")) {
        ssi.arm_ = Arm::Greedy;
    }  else if (options.aglsChooseArm.is("greedy_exploit")) {
        // compute ucb value of each arm
        double ucbValueGreedy = ssi.greedyRewards_ + options.aglsAssumptionUcbFactor.get() *
                                                         sqrt(log(ssi.totalConflicts_) / (ssi.greedyConflicts_ + 1));
        double ucbValueExploit = ssi.exploitRewards_ + options.aglsAssumptionUcbFactor.get() *
                                                           sqrt(log(ssi.totalConflicts_) / (ssi.exploitConflicts_ + 1));
        if (ucbValueExploit > ucbValueGreedy) {
            ssi.arm_ = Arm::Exploit;
        } else {
            ssi.arm_ = Arm::Greedy;
        }
    } else if (options.aglsChooseArm.is("greedy_linear")) {
        // compute ucb value of each arm
        double ucbValueGreedy = ssi.greedyRewards_ + options.aglsAssumptionUcbFactor.get() *
                                                         sqrt(log(ssi.totalConflicts_) / (ssi.greedyConflicts_ + 1));
        double ucbValueEmpty = ssi.emptyRewards_ + options.aglsAssumptionUcbFactor.get() *
                                                       sqrt(log(ssi.totalConflicts_) / (ssi.emptyConflicts_ + 1));
        if (ucbValueEmpty > ucbValueGreedy) {
            ssi.arm_ = Arm::Empty;
        } else {
            ssi.arm_ = Arm::Greedy;
        }
    } else if (options.aglsChooseArm.is("exploit_linear")) {
        // compute ucb value of each arm
        double ucbValueExploit = ssi.exploitRewards_ + options.aglsAssumptionUcbFactor.get() *
                                                           sqrt(log(ssi.totalConflicts_) / (ssi.exploitConflicts_ + 1));
        double ucbValueEmpty = ssi.emptyRewards_ + options.aglsAssumptionUcbFactor.get() *
                                                       sqrt(log(ssi.totalConflicts_) / (ssi.emptyConflicts_ + 1));
        if (ucbValueEmpty > ucbValueExploit) {
            ssi.arm_ = Arm::Empty;
        } else {
            ssi.arm_ = Arm::Exploit;
        }
    }

    // set new assumption
    if (ssi.state_ == SolveState::SAT || ssi.state_ == SolveState::INPROCESSED) {
        if (ssi.arm_ == Arm::Empty) {
            std::cout << "c empty assumption\n";
        } else if (ssi.arm_ == Arm::Exploit) {
            std::cout << "c exploit assumption\n";
        } else {
            std::cout << "c greedy assumption\n";
        }
        assumps.clear();
//        solver.ClearPhase();
        ssi.greedyRewards_ *= options.aglsBanditDecayFactor.get();
        ssi.exploitRewards_ *= options.aglsBanditDecayFactor.get();
        ssi.emptyRewards_ *= options.aglsBanditDecayFactor.get();

        if (ssi.arm_ == Arm::Greedy) {
            // randomly assume a set of falsified obj lits from incumbent solution to be satisfiable
            if (options.aglsAssumptionHeuristic.is("greedy")) {
                PickAssumptionByRandomGreedy(ssi);
            } else {
                std::cout << "Unexpected Error: invalid parameter\n";
                exit(-1);
            }
        } else if (ssi.arm_ == Arm::Exploit) {
            PropagateSatisfiedLiterals(ssi);
            PickAssumptionAndPropagate(ssi);
        } else if (ssi.arm_ == Arm::Empty) {
            assumps.clear();
        }
        std::cout << "c assumption size " << assumps.size() << "\n";
    } else if (ssi.state_ == SolveState::INCONSISTENT) {
        RemoveInconsistencyAll(ssi);
    }
}

void PropagateSatisfiedLiterals(SearchStateInformation& ssi)
{
    // initialize
    if (ssi.incumbentSolu_.empty()) {
        return;
    }
    int level = 0;
    solver.BackJumpTo(level);

    // add all satisfied objective literals (in incumbent solution) into assumption
    for (Var v : origObj->vars) {
        Lit l = ssi.incumbentSolu_[v];
        if (solver.IsTrue(l)) {
            // var v has been propagated to l
            continue;
        } else if (solver.IsFalse(l)) {
            // var v has been propagated to ~l
            continue;
        }

        if (origObj->getLit(v) == -l) {
            // var v has been satisfied in incumbent solution
            CeSuper confl = solver.DecideAndPropagate(l);
            if (confl) {
                solver.BackJumpTo(level);
                continue;
            }
            ++level;
        }
    }

    // set assumption
    assumps.clear();
    for (Lit l : solver.GetTrail()) {
        if (origObj->getLit(l) == 0 || !solver.IsDecided(l)) {
            continue;
        }
        assumps.add(l);
    }
}

void PickAssumptionAndPropagate(SearchStateInformation& ssi)
{
    if (ssi.incumbentSolu_.empty() || options.aglsAssumptionHeuristic.is("non")) {
        return;
    }

    // std::random_shuffle(ssi.falsifiedObjLits.begin(), ssi.falsifiedObjLits.end());
    std::vector<Lit> sampleRes;

    int i, j = 0;
    Var v;
    std::vector<Var> falsifiedVars(origObj->vars.size());
    std::vector<double> weight(origObj->vars.size());
    for (i = 0; i < origObj->vars.size(); ++i) {
        v = origObj->vars[i];
        if (origObj->getLit(v) == ssi.incumbentSolu_[v]) {
            falsifiedVars[j] = v;
            weight[j] = abs(static_cast<double>(origObj->getCoef(v)) / objAvgCoef_);
            ++j;
        }
    }
    falsifiedVars.resize(j);
    weight.resize(j);

    WeightedRandomSampling(1, falsifiedVars, weight, sampleRes);

    for (Lit l : sampleRes) {
        assumps.add(-origObj->getLit(l));
    }
}

void PickAssumptionByRandomGreedy(SearchStateInformation& ssi)
{
    if (ssi.state_ != SolveState::SAT && ssi.state_ != SolveState::INPROCESSED) {
        std::cout << "Unexpected Error: invalid solve state\n";
        exit(-1);
    }

    assumps.clear();
    Var v;
    Lit l;
    double coef;
    int i, j, index;
    double r;

    // reset all constraints
    for (i = 0; i < numConstr_; ++i) {
        satCount_[i] = 0;
        satSlack_[i] = constrCoefSum_[i];
    }

    bigint assumptionCost = 0, assumptionSat = 0;

    // begin to pick assumption
    bigint solutionImproveDegree = - normalized_upperbound + static_cast<bigint>(softWeightSum_);
    greedyAssignment_.resize(stats.NORIGVARS + 1);
    for (i = 0; i < orderedVarToCheck_.size(); ++i) {
        v = orderedVarToCheck_[i];
        double satDeltPos = 0, satDeltNeg = 0;

        // compute score from hard constraints
        for (auto& lit : varLit_[v]) {
            l = lit.lit_;
            coef = lit.coef_;
            index = lit.consId_;
            // skip satisfied or unsatisfied constraints
            if (satCount_[index] >= constrDegree_[index]) {
                continue;
            }
            // compute t_v and f_v
            if (l > 0) {
                satDeltPos += constrWeight_[index] *
                        fmin(coef / constrAvgCoef_[index], (constrDegree_[index] - satCount_[index]) / constrAvgCoef_[index]);
            } else {
                satDeltNeg += constrWeight_[index] *
                        fmin(coef / constrAvgCoef_[index], (constrDegree_[index] - satCount_[index]) / constrAvgCoef_[index]);
            }
        }
        // compute score from soft objective
        Lit objLit = -origObj->getLit(v);

        if (objLit != 0 && assumptionSat < solutionImproveDegree) {
            auto objCoef = static_cast<double>(aux::abs(origObj->getCoef(v)));
            if (objLit > 0) {
                satDeltPos += solutionImproveWeight_ * (objCoef / objAvgCoef_);
            } else {
                satDeltNeg += solutionImproveWeight_ * (objCoef / objAvgCoef_);
            }
        }

        // randomly select assumption
        Lit target = 0;
        if (satDeltPos > satDeltNeg) {
            target = v;
        } else if (satDeltPos < satDeltNeg) {
            target = -v;
        } else {
            r = (random() % 100000) * 1e-5;
            if (r < 0.5) {
                target = v;
            } else {
                target = -v;
            }
        }

//        ++count;
//        std::cout << "var " << v << "\n";
//        std::cout << "sat pos: " << satDeltPos << " unsat neg: " << unsatDeltNeg << "\n";
//        std::cout << "sat neg: " << satDeltNeg << " unsat pos: " << unsatDeltPos << "\n";

        if (target != 0 && target == -origObj->getLit(v)) {
            assumps.add(target);
            assumptionSat += aux::abs(origObj->coefs[v]);
        } else if (target != 0 && target == origObj->getLit(v)) {
            assumptionCost += aux::abs(origObj->coefs[v]);
        }

        // post process
        greedyAssignment_[v] = target;

        for (auto& lit : varLit_[v]) {
            l = lit.lit_;
            coef = lit.coef_;
            index = lit.consId_;
            if (l == target) {
                satCount_[index] += coef;
            } else {
                satSlack_[index] -= coef;
            }
        }
    }
//    solver.SetPhase(greedyAssignment_);
    int unsat = 0;
    for (i = 0; i < numConstr_; ++i) {
        if (satSlack_[i] < constrDegree_[i]) {
            ++unsat;
            constrWeight_[i] += 1;
        }
    }
    std::cout << "c num of unsat constraints " << unsat << "\n";

    std::cout << "c assumption cost " << assumptionCost << "\n";
    if (solver.foundSolution() && assumptionCost > normalized_upperbound) {
        solutionImproveWeight_ += 1;
        std::cout << "c increase the weight of solution-improve constraint to " << solutionImproveWeight_ << "\n";
    }
}

void PickPhaseByRandomGreedy(SearchStateInformation& ssi)
{
    if (ssi.state_ != SolveState::SAT && ssi.state_ != SolveState::INPROCESSED && ssi.state_ != SolveState::RESTARTED) {
        std::cout << "Unexpected Error: invalid solve state\n";
        exit(-1);
    }

    // compute global score
    Var v;
    double score;
    greedyAssignment_.resize(stats.NORIGVARS + 1);
    for (v = 1; v <= stats.NORIGVARS; ++v) {
        score = 0;
        for (const auto& lit : varLit_[v]) {
            score += lit.lit_ > 0 ?  static_cast<double>(lit.coef_) / constrAvgCoef_[lit.consId_] :
                                        -static_cast<double>(lit.coef_) / constrAvgCoef_[lit.consId_];
        }
        greedyAssignment_[v] = score > 0 ? v : -v;
    }
    solver.SetInputPhase(greedyAssignment_);
}

void Solve(SearchStateInformation& ssi)
{
    // remove unit literals in the assumption
    for (Lit l : assumps.getKeys()) {
        if (solver.IsUnit(l) || solver.IsUnit(-l)) {
            assumps.remove(l);
        }
    }
    // call CDCL solver
    long long conflictsNum = stats.NCONFL;
    solver.setAssumptions(assumps);
    SolveAnswer ans = solver.Solve(ssi.restartBudget_);
    ssi.totalConflicts_ += (stats.NCONFL - conflictsNum);
    if (ssi.arm_ == Arm::Greedy) {
        ssi.greedyConflicts_ += (stats.NCONFL - conflictsNum);
    } else if (ssi.arm_ == Arm::Exploit) {
        ssi.exploitConflicts_ += (stats.NCONFL - conflictsNum);
    } else if (ssi.arm_ == Arm::Empty) {
        ssi.emptyConflicts_ += (stats.NCONFL - conflictsNum);
    }

    // update ssi
    ssi.state_ = ans.state;
    if (ssi.state_ == SolveState::SAT) {
        ++ssi.numSolutions_;
        ssi.incumbentSolu_ = ans.solution;

        bigint newNormalizedUpperbound = 0;
        for (Var v : origObj->vars) {
            if (ssi.incumbentSolu_[v] == origObj->getLit(v)) {
                newNormalizedUpperbound += origObj->getCoef(origObj->getLit(v));
            }
        }

        if (ssi.arm_ == Arm::Greedy) {
            ssi.greedyRewards_ += static_cast<double>(normalized_upperbound - newNormalizedUpperbound) / static_cast<double>(normalized_upperbound);
        } else if (ssi.arm_ == Arm::Exploit) {
            ssi.exploitRewards_ += static_cast<double>(normalized_upperbound - newNormalizedUpperbound) / static_cast<double>(normalized_upperbound);
        } else if (ssi.arm_ == Arm::Empty) {
            ssi.emptyRewards_ += static_cast<double>(normalized_upperbound - newNormalizedUpperbound) / static_cast<double>(normalized_upperbound);
        }
    } else if (ssi.state_ == SolveState::INCONSISTENT) {
        ++ssi.numInconsistencies_;
        ssi.cores_ = std::move(ans.cores);
    } else if (ssi.state_ == SolveState::INPROCESSED) {
        ++ssi.numFails_;
    }
}

void UpdateUpperbound([[maybe_unused]] SearchStateInformation& ssi)
{
    // add upperbound constraint obj <= upper_bound - 1 into cdcl solver;
    const bigint prevUpperbound = normalized_upperbound;
    handleNewSolution(solver.lastSol);
    std::cout << "AGLS upperbound update to " << (bigint)upper_bound << " @ " << stats.getRunTime() << "s\n";
}

void RemoveInconsistencyAll(SearchStateInformation& ssi)
{
     // remove all derived unit lits from assumption
     for (Var v: reformObj->vars) {
         if (isUnit(solver.getLevel(), v) || isUnit(solver.getLevel(), -v)) {
             assumps.remove(v);
             assumps.remove(-v);
         }
     }

     // remove inconsistent lits from assumption
     for (CeSuper& core : ssi.cores_) {
         for (Var v : core->vars) {
             assumps.remove(v);
             assumps.remove(-v);
         }
     }
}

void RemoveInconsistencyRandomlyHalving(SearchStateInformation& ssi)
{
    // remove all derived unit lits from assumption
    for (Var v: reformObj->vars) {
        if (isUnit(solver.getLevel(), v) || isUnit(solver.getLevel(), -v)) {
            assumps.remove(v);
            assumps.remove(-v);
        }
    }

    // remove inconsistent lits from assumption
    for (CeSuper& core : ssi.cores_) {
        size_t removeNum = ceil(static_cast<float>(core->vars.size()) / 2);
        std::vector<double> weight;
        weight.resize(core->vars.size(), 1);
        std::vector<Var> res;
        WeightedRandomSampling(removeNum, core->vars, weight, res);

        for (Var v : res) {
            assumps.remove(v);
            assumps.remove(-v);
        }
    }
}

void ProcessExceedingConflictsBudget([[maybe_unused]] SearchStateInformation& ssi)
{
    // reduce learned constraints
    solver.ReduceDB();
}

void GetInitSolutionByMPIHeuristic(SearchStateInformation& ssi)
{
    // run CDCL solving
    std::cout << "AGLS begin to find initial solution by default heuristic  @ " << stats.getRunTime() << " s\n";
    PickPhaseByRandomGreedy(ssi);
    long long posPhaseConfl = 0, negPhaseConfl = 0, greedyPhaseConfl = 0, prevConfl = stats.NCONFL;
    while (true) {
        assumps.clear();
        solver.setAssumptions(assumps);

        if (greedyPhaseConfl < negPhaseConfl && greedyPhaseConfl < posPhaseConfl) {
            std::cout << "c greedy phase\n";
            solver.LoadInputPhase();
        } else if (posPhaseConfl < negPhaseConfl) {
            std::cout << "c positive phase\n";
            solver.LoadPositivePhase();
        } else {
            std::cout << "c negative phase\n";
            solver.LoadNegativePhase();
        }
        prevConfl = stats.NCONFL;
        SolveAnswer ans = solver.Solve(options.aglsInitRestartsBudget.get());

        if (greedyPhaseConfl < negPhaseConfl && greedyPhaseConfl < posPhaseConfl) {
            greedyPhaseConfl += (stats.NCONFL - prevConfl);
        } else if (posPhaseConfl < negPhaseConfl) {
            posPhaseConfl += (stats.NCONFL - prevConfl);
        } else {
            negPhaseConfl += (stats.NCONFL - prevConfl);
        }

        ssi.state_ = ans.state;
        if (ssi.state_ == SolveState::SAT) {
            // new solution found
            handleNewSolution(solver.lastSol);
            // print value of initial solution
            std::cout << "AGLS value of initial solution " << normalized_upperbound << " @ " << stats.getRunTime() << " s\n";
            break;
        } else if (ssi.state_ == SolveState::UNSAT) {
            // optimal solution found
            quit::exit_UNSAT(solver, upper_bound);
        } else if (ssi.state_ == SolveState::INPROCESSED) {
            ProcessExceedingConflictsBudget(ssi);
        }

        if (stats.getRunTime() >= options.time_limit.get()) {
            // out of time limit
            quit::exit_INDETERMINATE(solver);
        }
    }

    // finish CDCL solving
    std::cout << "AGLS searching for initial solution by default heuristic finished @ " << stats.getRunTime() << " s\n";
}

void GetInitSolutionByDefaultHeuristic(SearchStateInformation& ssi)
{
    // run CDCL solving
    std::cout << "AGLS begin to find initial solution by linear heuristic  @ " << stats.getRunTime() << " s\n";
    while (true) {
        assumps.clear();
        solver.setAssumptions(assumps);
        SolveAnswer ans = solver.Solve(options.aglsInitRestartsBudget.get());
        ssi.state_ = ans.state;
        if (ssi.state_ == SolveState::SAT) {
            // new solution found
            handleNewSolution(solver.lastSol);
            // print value of initial solution
            std::cout << "AGLS value of initial solution " << normalized_upperbound << " @ " << stats.getRunTime() << " s\n";
            break;
        } else if (ssi.state_ == SolveState::UNSAT) {
            // optimal solution found
            quit::exit_UNSAT(solver, upper_bound);
        } else if (ssi.state_ == SolveState::INPROCESSED) {
            ProcessExceedingConflictsBudget(ssi);
        }

        if (stats.getRunTime() >= options.time_limit.get()) {
            // out of time limit
            quit::exit_INDETERMINATE(solver);
        }
    }

    // finish CDCL solving
    std::cout << "AGLS searching for initial solution by linear heuristic finished @ " << stats.getRunTime() << " s\n";
}

void GetInitSolutionByGreedyHeuristic(SearchStateInformation& ssi)
{
    // improve initial solution
    std::cout << "AGLS begin to improve initial solution @ " << stats.getRunTime() << " s\n";
    assumps.clear();
    std::vector<Var> remainedObjVars = reformObj->vars;
    std::reverse(remainedObjVars.begin(), remainedObjVars.end());
    while (stats.getRunTime() < options.time_limit.get() && !remainedObjVars.empty()) {
        if (ssi.state_ == SolveState::SAT || ssi.state_ == SolveState::INPROCESSED) {
            // push a subset of remained variables into assumption
            size_t numRemained = remainedObjVars.size(), numToPush = ceil(static_cast<float>(numRemained) / 2);
            for (size_t i = 0; i < numToPush; ++i) {
                assumps.add(-origObj->getLit(remainedObjVars[numRemained - 1 - i]));
            }
            remainedObjVars.resize(numRemained - numToPush);
        } else if (ssi.state_ == SolveState::INCONSISTENT) {
            RemoveInconsistencyAll(ssi);
        }

        // CDCL solving
        Solve(ssi);

        // post process
        if (ssi.state_ == SolveState::SAT) {
            // new solution found
            UpdateUpperbound(ssi);
        } else if (ssi.state_ == SolveState::UNSAT) {
            // infeasibility has been proved
            quit::exit_UNSAT(solver, upper_bound);
        } else if (ssi.state_ == SolveState::INPROCESSED) {
            ProcessExceedingConflictsBudget(ssi);
        }

        if (stats.getRunTime() >= options.time_limit.get()) {
            // out of time limit
            quit::exit_INDETERMINATE(solver);
        }
    }

    // finish improving process
    std::cout << "AGLS improving initial solution finished @ " << stats.getRunTime() << " s\n";
}

void GetInitSolutionByStructureBasedPhase(SearchStateInformation& ssi)
{
    if (solver.foundSolution()) {
        return;
    }

    // initialize structure score
    solver.InitializeStructureInformation();

    // use structure phase solving
    std::cout << "AGLS begin to find initial solution using structure phase @ " << stats.getRunTime() << " s\n";
    while (stats.getRunTime() < options.time_limit.get()) {
        assumps.clear();
        solver.setAssumptions(assumps);
        SolveAnswer ans = solver.SolveWithStructurePhaseHeuristic(5);
        ssi.state_ = ans.state;
        if (ssi.state_ == SolveState::SAT) {
            // new solution found
            handleNewSolution(solver.lastSol);
            // print value of initial solution
            std::cout << "AGLS value of initial solution " << normalized_upperbound << " @ " << stats.getRunTime() << " s\n";
            break;
        } else if (ssi.state_ == SolveState::UNSAT) {
            // optimal solution found
            quit::exit_UNSAT(solver, upper_bound);
        } else if (ssi.state_ == SolveState::INPROCESSED) {
            ProcessExceedingConflictsBudget(ssi);
        }

        if (stats.getRunTime() >= options.time_limit.get()) {
            // out of time limit
            quit::exit_INDETERMINATE(solver);
        }
    }

    std::cout << "AGLS searching for initial solution using structure phase finished @ " << stats.getRunTime() << " s\n";
}

void GetInitSolutionByHybridHeuristic(SearchStateInformation& ssi)
{
    GetInitSolutionByMPIHeuristic(ssi);
    if (solver.foundSolution()) {
        GetInitSolutionByGreedyHeuristic(ssi);
    } else {
        GetInitSolutionByStructureBasedPhase(ssi);
    }
}

void GetInitSolutionByGreedyPhaseHeuristic (SearchStateInformation& ssi)
{
    // run CDCL solving
    std::cout << "AGLS begin to find initial solution by phase heuristic  @ " << stats.getRunTime() << " s\n";

    while (true) {
        assumps.clear();
        solver.setAssumptions(assumps);
        PickPhaseByRandomGreedy(ssi);
        SolveAnswer ans = solver.Solve(5);
        ssi.state_ = ans.state;
        if (ssi.state_ == SolveState::SAT) {
            // new solution found
            handleNewSolution(solver.lastSol);
            // print value of initial solution
            std::cout << "AGLS value of initial solution " << normalized_upperbound << " @ " << stats.getRunTime() << " s\n";
            break;
        } else if (ssi.state_ == SolveState::UNSAT) {
            // optimal solution found
            quit::exit_UNSAT(solver, upper_bound);
        } else if (ssi.state_ == SolveState::INPROCESSED) {
            ProcessExceedingConflictsBudget(ssi);
        }

        if (stats.getRunTime() >= options.time_limit.get()) {
            // out of time limit
            quit::exit_INDETERMINATE(solver);
        }
    }

    // finish CDCL solving
    std::cout << "AGLS searching for initial solution by default heuristic finished @ " << stats.getRunTime() << " s\n";
}

void InitializeGreedyAssumption()
{
    numConstr_ = solver.getNbConstraints();

    softWeightSum_ = static_cast<double>(origObj->absCoeffSum());
    if (origObj->vars.empty()) {
        objAvgCoef_ = 1;
    } else {
        objAvgCoef_ = softWeightSum_ / origObj->vars.size();
    }
    solutionImproveWeight_ = 1;
    varCount_.resize(stats.NORIGVARS + 1, 0);
    varLit_.resize(stats.NORIGVARS + 1);
    satCount_.resize(numConstr_, 0);
    satSlack_.resize(numConstr_, 0);
    constrDegree_.resize(numConstr_, 0);
    constrCoefSum_.resize(numConstr_, 0);
    constrAvgCoef_.resize(numConstr_, 0);
    constrWeight_.resize(numConstr_, 1);

//    orderedVarToCheck_.resize(origObj->vars.size());
    orderedVarToCheck_.resize(stats.NORIGVARS);
    std::vector<Lit> greedyAssignment(stats.NORIGVARS + 1);

    // initialize objective information
    int i = 0, j = 0;
    for (i = 1; i <= stats.NORIGVARS; ++i) {
        if (reformObj->getLit(i) == 0) {
            orderedVarToCheck_[j++] = i;
        }
    }
    reformObj->sortInDecreasingCoefOrder();
    size_t objSize = reformObj->vars.size();
    for (i = 0; i < objSize; ++i) {
        Var v = reformObj->vars[objSize - i - 1];
        orderedVarToCheck_[j++] = v;
    }

//    std::shuffle(orderedVarToCheck_.begin(), orderedVarToCheck_.end(), std::default_random_engine(0));

    // initialize constraints information
    for (i = 0; i < solver.getNbConstraints(); ++i) {
        auto& constr = solver.GetIthConstraint(i);
        for (j = 0; j < constr.size(); ++j) {
            ++varCount_[toVar(constr.lit(j))];
        }
    }
    for (Var v = 1; v <= stats.NORIGVARS; ++v) {
        varLit_[v].resize(varCount_[v]);
        varCount_[v] = 0;
    }
    for (i = 0; i < solver.getNbConstraints(); ++i) {
        auto& constr = solver.GetIthConstraint(i);
        constrDegree_[i] = static_cast<double>(constr.degree());
        for (j = 0; j < constr.size(); ++j) {
            Var v = toVar(constr.lit(j));
            long long coef = static_cast<long long>(constr.coef(j));
            int index = i;
            constrCoefSum_[i] += coef;
            varLit_[v][varCount_[v]].lit_ = constr.lit(j);
            varLit_[v][varCount_[v]].coef_ = coef;
            varLit_[v][varCount_[v]].consId_ = index;
            ++varCount_[v];
        }
        constrAvgCoef_[i] = constrCoefSum_[i] / constr.size();
    }

    // initialize fixed assumption
    Var v;
    Lit l;
    double coef;
    int index;
    for (i = 0; i < numConstr_; ++i) {
        satCount_[i] = 0;
        satSlack_[i] = constrCoefSum_[i];
    }
}

};

void decide();
void run(CeArb objective);

}  // namespace run

}  // namespace rs
