import copy
import time
import itertools

from lark import Tree
from z3 import SolverFor, Bool, Real, Or, sat, And, Implies, RealVal, Sum

import hyperprob.semanticencoder
from hyperprob.utility import common
from hyperprob import propertyparser
from hyperprob.semanticencoder import SemanticsEncoder

class ModelChecker:
    def __init__(self, model, hyperproperty, lengthOfStutter, maxSchedProb):
        self.model = model
        self.initial_hyperproperty = hyperproperty  # object of property class
        self.solver = SolverFor("QF_NRA")
        self.stutterLength = lengthOfStutter  # default value 1 equals no stuttering
        self.maxSchedProb = maxSchedProb
        self.list_of_subformula = []
        self.dictOfReals = dict()
        self.dictOfBools = dict()
        self.no_of_subformula = 0
        self.no_of_state_quantifier = 0
        self.no_of_stutter_quantifier = 0
        self.stutter_state_mapping = None  # value at index of stutter variable is the corresponding state variable

    def modelCheck(self):
        # parse property
        stutter_quantified_property, self.no_of_state_quantifier, state_indices = propertyparser.checkStateQuantifiers(
            copy.deepcopy(self.initial_hyperproperty.parsed_property))
        non_quantified_property, self.stutter_state_mapping = propertyparser.checkStutterQuantifiers(
            stutter_quantified_property.children[0], state_indices)
        self.no_of_stutter_quantifier = len(self.stutter_state_mapping.keys())
        self.no_of_state_quantifier = len(set(self.stutter_state_mapping.values()))
        non_quantified_property = non_quantified_property.children[0]
        self.addToSubformulaList(non_quantified_property)

        start_time = time.perf_counter()
        # encode scheduler and stutter-schedulers
        self.encodeScheduler()
        self.encodeStuttering()

        # encode the meaning of the quantifiers
        self.truth()

        # encode the non-quantified property
        common.colourinfo("\nEncoding non-quantified formula...", False)
        semanticEncoder = SemanticsEncoder(self.model, self.solver,
                                           self.list_of_subformula,
                                           self.dictOfReals, self.dictOfBools,
                                           self.no_of_subformula,
                                           self.no_of_state_quantifier, self.no_of_stutter_quantifier,
                                           self.stutterLength,
                                           self.stutter_state_mapping
                                           )
        semanticEncoder.encodeSemantics(non_quantified_property)

        # ensure that all variables encoding probabilities range in [0, 1]
        restrictions = []
        for name in self.dictOfReals.keys():
            if name[0] == 'p':
                restrictions.append(And(self.dictOfReals[name] >= RealVal(0), self.dictOfReals[name] <= RealVal(1)))
        self.solver.add(restrictions)
        self.no_of_subformula += 1

        encoding_time = time.perf_counter() - start_time
        common.colourinfo("\nTime to encode in seconds: " + str(round(encoding_time, 2)), False)

        self.printResult()

    def encodeScheduler(self):
        """
        Introduce variables encoding the probabilistic memoryless scheduler which satisfies the following:
        if Act(s) = Act(s'), then act(s, alpha) = act(s', alpha) for all alpha in Act(s).
        Variable a_A_x represents the probability of choosing action x at a state with enabled actions A
        """
        common.colourinfo("Encoding scheduler...")
        set_of_actionsets = {frozenset(x) for x in self.model.getDictOfActions().values()}
        scheduler_restrictions = []

        for A in set_of_actionsets:
            sum_over_probs = []
            # if only a single action is enabled at s, then that action will always be chosen with probability 1
            if len(A) == 1:
                action = list(A)[0]
                name = "a_" + str(set(A)) + "_" + str(action)
                self.addToVariableList(name)
                scheduler_restrictions.append(self.dictOfReals[name] == RealVal(1)) # .as_fraction()
            else:
                for action in A:
                    name = "a_" + str(set(A)) + "_" + str(action)
                    self.addToVariableList(name)
                    # probabilistic scheduler
                    maxVal = self.maxSchedProb
                    minVal = 1 - maxVal
                    scheduler_restrictions.append(self.dictOfReals[name] >= RealVal(minVal))
                    scheduler_restrictions.append(self.dictOfReals[name] <= RealVal(maxVal))
                    sum_over_probs.append(self.dictOfReals[name])
                scheduler_restrictions.append(Sum(sum_over_probs) == RealVal(1))

        self.solver.add(And(scheduler_restrictions))
        self.no_of_subformula += 1

    def encodeStuttering(self):
        """
        Introduce variables encoding:
        - the deterministic bounded-memory stutter-schedulers,
        - whether potential successor state is indeed a successor state under the encoded stutter-scheduler
        - the probability of moving to a successor under the encoded stutter-scheduler
        Variable t_i_s_x represents the stutter duration for stutter quantifier i and state s and action x.
        """

        # encode the stutter-schedulers
        common.colourinfo("Encoding stutter-schedulers...", False)
        list_over_quantifiers = []
        for quantifier in range(0, self.no_of_stutter_quantifier):
            list_over_states = []
            for state in self.model.parsed_model.states:
                list_over_actions = []
                for action in state.actions:
                    list_of_equations = []
                    name = "t_" + str(quantifier + 1) + "_" + str(state.id) + "_" + str(action.id)
                    self.addToVariableList(name)
                    for stutter_length in range(0, self.stutterLength):
                        list_of_equations.append(self.dictOfReals[name] == RealVal(stutter_length))
                    list_over_actions.append(Or(list_of_equations))
                    self.no_of_subformula += 1
                list_over_states.append(And(list_over_actions))
                self.no_of_subformula += 1
            list_over_quantifiers.append(And(list_over_states))
            self.no_of_subformula += 1
        self.solver.add(And(list_over_quantifiers))
        self.no_of_subformula += 1

        # encode probability of transitioning to successor under encoded stutter-scheduler and
        # whether potential successor state is indeed a successor state under the encoded stutter-scheduler
        common.colourinfo("Encoding transitions and probabilities under stutter-schedulers...", False)
        states_with_stutter = list(itertools.product(self.model.getListOfStates(), list(range(self.stutterLength))))
        list_over_quants = []
        list_over_quants_go = []
        for i in range(1, self.no_of_stutter_quantifier + 1):
            list_over_states = []
            list_over_states_go = []
            for state_stutter in states_with_stutter:
                list_over_actions = []
                list_over_actions_go = []
                for action in self.model.dict_of_acts[state_stutter[0]]:
                    list_over_succs = []
                    list_over_succs_go = []
                    succ = self.model.dict_of_acts_tran[str(state_stutter[0]) + " " + str(action)]
                    mdp_successor_list = []
                    dict_of_probs = {}
                    for s in succ:
                        space = s.find(' ')
                        succ_state = int(s[0:space])
                        mdp_successor_list.append((succ_state, 0))
                        dict_of_probs[(succ_state, 0)] = RealVal(s[space + 1:])

                    # mdp successors
                    for succ in mdp_successor_list:
                        # Tr
                        stu_name = "t_" + str(i) + "_" + str(state_stutter[0]) + "_" + str(action)
                        tr = "Tr_" + str(i) + "_" + str(state_stutter) + "_" + str(action) + "_" + str(succ)
                        self.addToVariableList(tr)

                        restriction = Or(self.dictOfReals[tr] == RealVal(0), self.dictOfReals[tr] == dict_of_probs[succ])
                        stutter = Implies(state_stutter[1] >= self.dictOfReals[stu_name],
                                          self.dictOfReals[tr] == dict_of_probs[succ])
                        cont = Implies(state_stutter[1] < self.dictOfReals[stu_name],
                                       self.dictOfReals[tr] == RealVal(0))
                        list_over_succs.append(And(restriction, stutter, cont))
                        self.no_of_subformula += 1

                        # go
                        go = "go_" + str(i) + "_" + str(state_stutter) + "_" + str(action) + "_" + str(succ)
                        self.addToVariableList(go)
                        pseudo_bool = Or(self.dictOfReals[go] == 0, self.dictOfReals[go] == 1)
                        stutter_go = And(state_stutter[1] < self.dictOfReals[stu_name],
                                      succ[1] == state_stutter[1] + 1)
                        cont_go = And(state_stutter[1] >= self.dictOfReals[stu_name],
                                   succ[1] == 0)

                        list_over_succs_go.append(And(pseudo_bool,
                                                      And(Implies(self.dictOfReals[go] == 1, Or(stutter_go, cont_go)),
                                                          Implies(Or(cont_go, stutter_go), self.dictOfReals[go] == 1))))
                        self.no_of_subformula += 2

                    # stutter successor
                    if state_stutter[1] < self.stutterLength - 1:
                        stu_name = "t_" + str(i) + "_" + str(state_stutter[0]) + "_" + str(action)

                        # Tr
                        succ = (state_stutter[0], state_stutter[1] + 1)
                        tr = "Tr_" + str(i) + "_" + str(state_stutter) + "_" + str(action) + "_" + str(succ)
                        self.addToVariableList(tr)

                        restriction = Or(self.dictOfReals[tr] == RealVal(0), self.dictOfReals[tr] == RealVal(1))
                        stutter = Implies(state_stutter[1] >= self.dictOfReals[stu_name],
                                          self.dictOfReals[tr] == RealVal(0))
                        cont = Implies(state_stutter[1] < self.dictOfReals[stu_name],
                                       self.dictOfReals[tr] == RealVal(1))
                        list_over_succs.append(And(restriction, stutter, cont))
                        self.no_of_subformula += 1

                        # go
                        go = "go_" + str(i) + "_" + str(state_stutter) + "_" + str(action) + "_" + str(succ)
                        self.addToVariableList(go)
                        pseudo_bool = Or(self.dictOfReals[go] == 0, self.dictOfReals[go] == 1)
                        stutter_go = And(state_stutter[1] < self.dictOfReals[stu_name],
                                         succ[1] == state_stutter[1] + 1)
                        cont_go = And(state_stutter[1] >= self.dictOfReals[stu_name],
                                      succ[1] == 0)

                        list_over_succs_go.append(And(pseudo_bool,
                                                      And(Implies(self.dictOfReals[go] == 1, Or(stutter_go, cont_go)),
                                                          Implies(Or(cont_go, stutter_go), self.dictOfReals[go] == 1))))
                        self.no_of_subformula += 2

                    list_over_actions.append(And(list_over_succs))
                    self.no_of_subformula += 1
                    list_over_actions_go.append(And(list_over_succs_go))
                    self.no_of_subformula += 1
                list_over_states.append(And(list_over_actions))
                self.no_of_subformula += 1
                list_over_states_go.append(And(list_over_actions_go))
                self.no_of_subformula += 1
            list_over_quants.append(And(list_over_states))
            self.no_of_subformula += 1
            list_over_quants_go.append(And(list_over_states_go))
            self.no_of_subformula += 1
        self.solver.add(And(list_over_quants))
        self.no_of_subformula += 1
        self.solver.add(And(list_over_quants_go))
        self.no_of_subformula += 1

    def truth(self):
        """
        Encode the state quantifiers by translating "forall" to conjunction and "exists" to disjunction
        """
        # cycle through property and collect forall, exist
        list_of_state_AV = []  # will have the OR, AND according to the quantifier in that index in the formula
        # TODO: work to remove assumption of stutter schedulers named in order
        common.colourinfo("Prepare encoding quantifiers...", False)
        changed_hyperproperty = self.initial_hyperproperty.parsed_property
        while len(changed_hyperproperty.children) > 0:
            if changed_hyperproperty.data in ['exist_scheduler', 'forall_scheduler']:
                changed_hyperproperty = changed_hyperproperty.children[1]
            elif changed_hyperproperty.data == 'exist_state':
                if int(changed_hyperproperty.children[0].value[1:]) in self.stutter_state_mapping.values():
                    list_of_state_AV.append('V')
                changed_hyperproperty = changed_hyperproperty.children[1]
            elif changed_hyperproperty.data == 'forall_state':
                if int(changed_hyperproperty.children[0].value[1:]) in self.stutter_state_mapping.values():
                    list_of_state_AV.append('A')
                changed_hyperproperty = changed_hyperproperty.children[1]
            elif changed_hyperproperty.data == 'exist_stutter':
                changed_hyperproperty = changed_hyperproperty.children[2]
            elif changed_hyperproperty.data in ['quantifiedformulastutter', 'quantifiedformulastate']:
                changed_hyperproperty = changed_hyperproperty.children[0]
            else:
                break

        index_of_phi = self.list_of_subformula.index(changed_hyperproperty)

        # create list of state tuples of the induced DTMC
        list_of_states_with_initial_stutter = list(itertools.product(self.model.getListOfStates(), [0]))
        list_of_state_tuples = list(
            itertools.product(list_of_states_with_initial_stutter, repeat=self.no_of_state_quantifier))
        if self.no_of_stutter_quantifier != self.no_of_state_quantifier:
            combined_list_of_states_with_initial_stutter = [
                tuple([x[self.stutter_state_mapping[q] - 1] for q in range(1, self.no_of_stutter_quantifier + 1)])
                for x in list_of_state_tuples]
        else:
            combined_list_of_states_with_initial_stutter = list_of_state_tuples

        # create list of holds_(s1,0)_..._0 for all state combinations
        list_of_holds = []
        for i in range(len(combined_list_of_states_with_initial_stutter)):
            name = "holds_"
            for j in range(self.no_of_stutter_quantifier):
                name += str(combined_list_of_states_with_initial_stutter[i][j]) + "_"
            name += str(index_of_phi)
            self.addToVariableList(name)
            list_of_holds.append(self.dictOfBools[name])

        # iteratively encode state quantifiers
        common.colourinfo("Encoding state quantifiers...", False)
        state_encoding_i = []
        state_encoding_ipo = list_of_holds
        for quant in range(self.no_of_state_quantifier, 0, -1):
            n = len(self.model.getListOfStates())
            len_i = int(len(state_encoding_ipo) / n)
            if list_of_state_AV[quant - 1] == 'A':
                state_encoding_i = [And(state_encoding_ipo[(j * n):((j + 1) * n)]) for j in range(len_i)]
            elif list_of_state_AV[quant - 1] == 'V':
                state_encoding_i = [Or(state_encoding_ipo[(j * n):((j + 1) * n)]) for j in range(len_i)]
            self.no_of_subformula += len_i
            state_encoding_ipo.clear()
            state_encoding_ipo = copy.deepcopy(state_encoding_i)
            state_encoding_i.clear()
        self.solver.add(state_encoding_ipo[0])

    def addToVariableList(self, name):
        if name[0] == 'h' and not name.startswith('holdsToInt'):  # holds_
            self.dictOfBools[name] = Bool(name)
        elif name[0] in ['p', 'd', 'a', 't', 'g', 'T'] or name.startswith('holdsToInt'):  # prob_, d_, a_, t_, go_, Tr_
            self.dictOfReals[name] = Real(name)

    def addToSubformulaList(self, formula_phi):
        """
        Add formula and all its subformulas to a list of all subformulas.
        The position of a subformula in this list is used to index the variables encoding meaning of the formula.
        :param formula_phi: subformula to be added to list
        """
        if formula_phi.data in ['exist_scheduler', 'forall_scheduler', 'exist_state', 'forall_state']:
            formula_phi = formula_phi.children[1]
            self.addToSubformulaList(formula_phi)
        elif formula_phi.data in ['and', 'or', 'implies', 'equivalent',
                                  'less_probability', 'equal_probability', 'greater_probability',
                                  'greater_and_equal_probability', 'less_and_equal_probability',
                                  'less_reward', 'equal_reward', 'greater_reward', 'greater_and_equal_reward',
                                  'less_and_equal_reward',
                                  'add_probability', 'subtract_probability', 'multiply_probability',
                                  'add_reward', 'subtract_reward', 'multiply_reward',
                                  'until_unbounded'
                                  ]:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            left_child = formula_phi.children[0]
            self.addToSubformulaList(left_child)
            right_child = formula_phi.children[1]
            self.addToSubformulaList(right_child)
        elif formula_phi.data in ['atomic_proposition', 'true', 'constant_probability', 'constant_reward']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
        elif formula_phi.data in ['next', 'not', 'future', 'global']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            self.addToSubformulaList(formula_phi.children[0])
        elif formula_phi.data in ['probability']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            self.addToSubformulaList(formula_phi.children[0])
        elif formula_phi.data in ['reward']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
                prob_formula = Tree('probability', [formula_phi.children[1]])
                self.list_of_subformula.append(prob_formula)
            self.addToSubformulaList(formula_phi.children[1])
        elif formula_phi.data in ['until_bounded']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            left_child = formula_phi.children[0]
            self.addToSubformulaList(left_child)
            right_child = formula_phi.children[3]
            self.addToSubformulaList(right_child)

    def checkResult(self):
        """
        Check whether the created SMT formula holds.
        :return:
            - truth: result of SMT solver
            - scheduler_assignments: list of variables encoding the scheduler and their assigned values
            - set_of_holds: set of state tuples that satisfy the formula
            - stuttersched_assignments: list of variables encoding the stutter-schedulers and their assigned values
            - statistics: statistics of the z3 solver
            - smt_time: time the SMT solver took to check the formula
        """
        common.colourinfo("\nChecking SMT-formula...", False)
        common.colourinfo(
            "Number of variables: " +
            str(len(self.dictOfReals.keys()) + len(self.dictOfBools.keys())),
            False)
        common.colourinfo("Number of formulas to check: " + str(self.no_of_subformula), False)
        starting_time = time.perf_counter()
        truth = self.solver.check()
        smt_time = time.perf_counter() - starting_time
        common.colourinfo("Finished checking!", False)
        common.colourinfo("Time required by z3 in seconds: " + str(round(smt_time, 2)), False)

        # collect information for printing
        scheduler_assignments = []
        set_of_holds = set()
        stuttersched_assignments = []
        other = []
        if truth == sat:
            z3model = self.solver.model()
            list_of_corr_stutter_qs = [[k for k, v in self.stutter_state_mapping.items() if v == q + 1] for q in range(self.no_of_state_quantifier)]

            for li in z3model:
                if li.name()[0] == 'h' and z3model[li] and li.name().split("_")[-1] == '0':
                    state_tuples_list = li.name().split("_")[1:-1]
                    states_list = [elt.split(", ")[0][1:] for elt in state_tuples_list]
                    stutter_set = {elt.split(", ")[1][:-1] for elt in state_tuples_list}
                    states_by_state_qs = [[states_list[i-1] for i in x] for x in list_of_corr_stutter_qs]

                    if stutter_set == {'0'} and {len(set(x)) for x in states_by_state_qs} == {1}:
                        state_list = [x[0] for x in states_by_state_qs]
                        set_of_holds.add(tuple(state_list))
                elif li.name()[0] == 'a':
                    scheduler_assignments.append((li.name(), z3model[li]))
                elif li.name()[0] == 't':
                    stuttersched_assignments.append((li.name(), z3model[li]))

            other.sort()
            for x in other:
                print(x)
        return truth, scheduler_assignments, set_of_holds, stuttersched_assignments, self.solver.statistics()

    def printResult(self):
        """
        Print the result of the model checking
        :param encoding_time: time it took to create the SMT encoding
        """
        smt_result, scheduler_assignments, holds, stuttersched_assignments, statistics = self.checkResult()
        scheduler_assignments.sort()
        stuttersched_assignments.sort()

        if smt_result.r == 1:
            # todo adjust to more fine-grained output depending on different quantifier combinations?
            common.colouroutput("The property HOLDS!")
            print("\nThe values of variables of the witness are:")
            print("Choose scheduler probabilities as follows:")
            for act_prob in scheduler_assignments:
                common.colouroutput(
                    "At a state with enabled actions " + act_prob[0].split("_")[1] +
                    " choose action " + act_prob[0].split("_")[2] +
                    " with probability " + str(act_prob[1]),
                    False)
            print("\nChoose stutterschedulers as follows:")
            for stutter_step in stuttersched_assignments:
                common.colouroutput(
                    "For quantifier t" + stutter_step[0].split("_")[1] +
                    " : For state " + stutter_step[0].split("_")[2] +
                    " and action " + stutter_step[0].split("_")[3] +
                    " choose stuttering duration " + str(stutter_step[1]),
                    False)
            print("\nThe following state variable assignments (s1, ..., sn) satisfy the property:")
            print(holds)
        elif smt_result.r == -1:
            common.colourerror("The property DOES NOT hold!")
        else:
            common.colourerror("Solver returns unknown")
        common.colourinfo("\nz3 statistics:", False)
        common.colourinfo(str(statistics), False)
