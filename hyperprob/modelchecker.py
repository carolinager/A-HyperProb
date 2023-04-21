import copy
import time
import itertools

from lark import Tree
from z3 import Solver, Bool, Real, Int, Or, sat, And, Implies, RealVal, Sum

from hyperprob.utility import common
from hyperprob import propertyparser
from hyperprob.sementicencoder import SemanticsEncoder


class ModelChecker:
    def __init__(self, model, hyperproperty, lengthOfStutter, dontRestrictSched=False):
        self.model = model
        self.initial_hyperproperty = hyperproperty  # object of property class
        self.solver = Solver()
        self.stutterLength = lengthOfStutter  # default value 1 (no stutter)
        self.list_of_subformula = []
        self.dictOfReals = dict()
        self.dictOfBools = dict()
        self.dictOfInts = dict()
        self.no_of_subformula = 0
        self.no_of_state_quantifier = 0
        self.no_of_stutter_quantifier = 0
        self.stutter_state_mapping = None  # value at index of stutter variable is the corresponding state variable
        self.dict_pair_index = dict() # dictionary mapping all state-action-pairs to their index in the tuples representing the stutter-schedulers
        self.dontRestrictSched = dontRestrictSched

    def modelCheck(self):
        non_quantified_property, self.no_of_state_quantifier, state_indices = propertyparser.checkStateQuantifiers(
            copy.deepcopy(self.initial_hyperproperty.parsed_property))
        non_quantified_property, self.stutter_state_mapping = propertyparser.checkStutterQuantifiers(
            non_quantified_property.children[0], state_indices)
        self.no_of_stutter_quantifier = len(self.stutter_state_mapping.keys())
        self.no_of_state_quantifier = len(set(self.stutter_state_mapping.values()))
        non_quantified_property = non_quantified_property.children[0]
        start_time = time.perf_counter()
        self.encodeActions()
        list_of_states_with_initial_stutter = list(itertools.product(self.model.getListOfStates(), [0]))
        combined_list_of_states_with_initial_stutter = list(
            itertools.product(list_of_states_with_initial_stutter, repeat=self.no_of_stutter_quantifier))

        if self.initial_hyperproperty.parsed_property.data == 'exist_scheduler':
            self.addToSubformulaList(non_quantified_property) # todo dont really need nq property here anymore
            self.truth(combined_list_of_states_with_initial_stutter)
            smt_end_time = time.perf_counter() - start_time
            self.printResult(smt_end_time, 'exists')

        elif self.initial_hyperproperty.parsed_property.data == 'forall_scheduler':
            negated_non_quantified_property = propertyparser.negateForallProperty(
                self.initial_hyperproperty.parsed_property)
            self.addToSubformulaList(negated_non_quantified_property)
            self.truth(combined_list_of_states_with_initial_stutter)
            smt_end_time = time.perf_counter() - start_time
            print("Finished Checking")
            self.printResult(smt_end_time, 'forall')

    def encodeActions(self):
        if self.dontRestrictSched:
            # probabilistic scheduler without extra restrictions:
            scheduler_probs = []
            for state in self.model.parsed_model.states:
                name = "a_" + str(state.id) + "_"  # a_s_x is probability of action x in state s
                sum_of_probs = RealVal(0)
                for act in state.actions:
                    name_a = name + str(act.id)
                    self.addToVariableList(name_a)
                    sum_of_probs += self.dictOfReals[name_a]
                scheduler_probs.append(sum_of_probs == RealVal(1))
            self.solver.add(And(scheduler_probs))
            self.no_of_subformula += 1
        else:
            # encode global, state-independent scheduler probabilities for the actions
            set_of_actions = set(itertools.chain.from_iterable(self.model.getDictOfActions().values()))
            if len(set_of_actions) > 2:
                raise ValueError(f"Model contains more than 2 different actions.")
            scheduler_restrictions = []
            sum_over_probs = []

            for action in set_of_actions:
                name = "a_" + str(action)  # a_x is probability of action x
                self.addToVariableList(name)
                scheduler_restrictions.append(self.dictOfReals[name] >= RealVal(0))
                scheduler_restrictions.append(self.dictOfReals[name] <= RealVal(1))
                sum_over_probs.append(self.dictOfReals[name])
            scheduler_restrictions.append(Sum(sum_over_probs) == RealVal(1))
            self.solver.add(And(scheduler_restrictions))
            self.no_of_subformula += 1

            # encode scheduler probabilities for each state
            state_scheduler_probs = []
            for state in self.model.parsed_model.states:
                name = "a_" + str(state.id) + "_"  # a_s_x is probability of action x in state s
                available_actions = list(state.actions)
                if len(available_actions) == 1:
                    name += str(available_actions[0].id)
                    self.addToVariableList(name)
                    state_scheduler_probs.append(self.dictOfReals[name] == RealVal(1))  # todo float(1) ??
                elif len(available_actions) == 2:
                    for action in available_actions:
                        name_x = name + str(action.id)
                        self.addToVariableList(name_x)
                        state_scheduler_probs.append(self.dictOfReals[name_x] == self.dictOfReals["a_" + str(action.id)])
            self.solver.add(state_scheduler_probs)
            self.no_of_subformula += 1

        common.colourinfo("Encoded actions in the MDP...")


    def addToVariableList(self, name):
        if name[0] == 'h' and not name.startswith('holdsToInt'):  # holds_
            self.dictOfBools[name] = Bool(name)
        elif name[0] in ['p', 'd', 'r', 'a', 's'] or name.startswith('holdsToInt'):  # prob_, d_, rew_, a_s, sigma_a
            self.dictOfReals[name] = Real(name)
        elif name[0] in ['t']:  # t_
            self.dictOfInts[name] = Int(name)

    def addToSubformulaList(self, formula_phi):
    # add as you go any new subformula part as needed
    # also adds all subformulas of the formula to the list
    # todo could be made more efficient: test whether formula_phi is in list only once in the beginning?
        if formula_phi.data in ['exist_scheduler', 'forall_scheduler', 'exist_state', 'forall_state']:
            formula_phi = formula_phi.children[1]
            self.addToSubformulaList(formula_phi)
        elif formula_phi.data in ['and', 'or', 'implies', 'biconditional',
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

    def genComposedStutterscheds(self, possible_stutterings, rel_quant_stu):
        list_of_lists = []
        for i in range(self.no_of_stutter_quantifier):
            if i+1 in rel_quant_stu:
                list_of_lists.append(possible_stutterings)
            else:
                list_of_lists.append([possible_stutterings[0]])

        return list(itertools.product(*list_of_lists))


    def truth(self, combined_list_of_states_with_initial_stutter):
        # corresponds to Algo 5 "Truth"
        # encode quantifiers, i.e. translate forall to And and exists to Or
        list_of_state_AV = []  # will have the OR, AND according to the quantifier in that index in the formula
        list_of_stutter_AV = []  # placeholder to manage stutter quantifier encoding
        # TODO (optional): work to remove assumption of stutter schedulers named in order
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
            elif changed_hyperproperty.data == 'forall_stutter':
                if int(changed_hyperproperty.children[0].value[1:]) in self.stutter_state_mapping.keys():
                    list_of_stutter_AV.append('AT')
                changed_hyperproperty = changed_hyperproperty.children[2]
            elif changed_hyperproperty.data == 'exist_stutter':
                if int(changed_hyperproperty.children[0].value[1:]) in self.stutter_state_mapping.keys():
                    list_of_stutter_AV.append('VT')
                changed_hyperproperty = changed_hyperproperty.children[2]
            elif changed_hyperproperty.data in ['quantifiedformulastutter', 'quantifiedformulastate']:
                changed_hyperproperty = changed_hyperproperty.children[0]
            else:
                break
        # TODO: read and track relevant quantifiers ->  Done in a way

        # changed_hyperproperty is now phi^nq, the outermost non-quantified formula
        index_of_phi = self.list_of_subformula.index(changed_hyperproperty)

        # create all possible stutter-schedulers: assign one stutter-length to each state-action-pair
        i = 0
        for state in self.model.parsed_model.states:
            for action in state.actions:
                self.dict_pair_index[(state.id, action.id)] = i
                i += 1
        possible_stutterings = list(itertools.product(list(range(self.stutterLength)), repeat=i)) # list of all possible functions f : S x Act -> {0, ..., stutterLength - 1}, represented as tuples
        combined_stutterscheds = list(itertools.product(possible_stutterings, repeat=self.no_of_stutter_quantifier))

        # create semantic encoding for each possible combination of stutter-schedulers
        common.colourinfo("Start encoding non-quantified formula for all possible stutter-schedulers... (this might take some time)", False)
        dict_of_encodings = dict()
        dict_of_rel_stutterscheds = dict()
        semanticEncoder = SemanticsEncoder(self.model, self.solver,
                                           self.list_of_subformula,
                                           self.dictOfReals, self.dictOfBools, self.dictOfInts,
                                           self.no_of_subformula,
                                           self.no_of_state_quantifier, self.no_of_stutter_quantifier,
                                           self.stutterLength,
                                           self.stutter_state_mapping, self.dict_pair_index)
        # encoding for trivial stutter-scheduler and calculating relevant stutterscheds
        _, rel_quant_stu, enc = semanticEncoder.encodeSemantics(changed_hyperproperty, combined_stutterscheds[0])
        dict_of_encodings[combined_stutterscheds[0]] = enc
        dict_of_rel_stutterscheds[combined_stutterscheds[0]] = semanticEncoder.genRelStutterscheds(
            combined_stutterscheds[0], rel_quant_stu)

        combined_stutterscheds_rel = self.genComposedStutterscheds(possible_stutterings, rel_quant_stu)

        # encoding for relevant other stutter-schedulers
        for stutter_scheds in combined_stutterscheds_rel[1:]:
            _, rel_quant_stu, enc = semanticEncoder.encodeSemantics(changed_hyperproperty, stutter_scheds)
            dict_of_encodings[stutter_scheds] = enc
            dict_of_rel_stutterscheds[stutter_scheds] = semanticEncoder.genRelStutterscheds(stutter_scheds,
                                                                                            rel_quant_stu)
            # todo unnecessary to keep relquantstu and calculate genRelStu due to ranging over combined_stutterscheds_rel already

            # todo introduce some dummy variable t_stutter_scheds s.t.  t_stutter_scheds iff encoding(stutter_scheds)
            # only for outputting purposes
        common.colourinfo("Finished encoding non-quantified formula...", False)

        list_of_prob_restrict = []
        for name in self.dictOfReals.keys():
            if name[0] == 'p':
                list_of_prob_restrict.append(self.dictOfReals[name] >= RealVal(0))
                list_of_prob_restrict.append(self.dictOfReals[name] <= RealVal(1))
        self.solver.add(And(list_of_prob_restrict))

        # create list of holds_(s1,0)_..._0 for all state combinations and for all relevant stutter-scheds
        list_of_holds_and_enc = []
        for i in range(len(combined_list_of_states_with_initial_stutter)):
            name = "holds_"
            for j in range(self.no_of_state_quantifier):
                name += str(combined_list_of_states_with_initial_stutter[i][j]) + "_"
            name += str(index_of_phi)

            for stutter_scheds in combined_stutterscheds_rel:
                name_s = name + "_" + str(dict_of_rel_stutterscheds[stutter_scheds])
                self.addToVariableList(name_s)
                list_of_holds_and_enc.append(And(self.dictOfBools[name_s], And(dict_of_encodings[stutter_scheds])))
            self.no_of_subformula += 2

        # encode stutter scheduler quantifiers (for each possible assignment of the state variables)
        stutter_encoding_i = []
        stutter_encoding_ipo = list_of_holds_and_enc
        for quant in range(self.no_of_stutter_quantifier, 0, -1):  # n, ..., 1
            # todo this needs to change
            if quant in rel_quant_stu:
                n = len(possible_stutterings)
                len_i = int(len(stutter_encoding_ipo) / n)
                if list_of_stutter_AV[quant - 1] == 'AT':
                    stutter_encoding_i = [And(stutter_encoding_ipo[(j * n):((j + 1) * n)]) for j in range(len_i)]
                elif list_of_stutter_AV[quant - 1] == 'VT':
                    stutter_encoding_i = [Or(stutter_encoding_ipo[(j * n):((j + 1) * n)]) for j in range(len_i)]
            else:
                stutter_encoding_i = copy.deepcopy(stutter_encoding_ipo)
            self.no_of_subformula += 1
            stutter_encoding_ipo.clear()
            stutter_encoding_ipo = copy.deepcopy(stutter_encoding_i)
            stutter_encoding_i.clear()
        common.colourinfo("Encoded stutter quantifiers", False)

        # iteratively encode state quantifiers
        # TODO adjust if we choose to allow several stutter-quant for a state-quant
        state_encoding_i = []
        state_encoding_ipo = stutter_encoding_ipo
        for quant in range(self.no_of_stutter_quantifier, 0, -1):
            n = len(self.model.getListOfStates())
            len_i = int(len(state_encoding_ipo) / n)
            if list_of_state_AV[quant - 1] == 'A':
                state_encoding_i = [And(state_encoding_ipo[(j * n):((j + 1) * n)]) for j in range(len_i)]
            elif list_of_state_AV[quant - 1] == 'V':
                state_encoding_i = [Or(state_encoding_ipo[(j * n):((j + 1) * n)]) for j in range(len_i)]
            self.no_of_subformula += 1
            state_encoding_ipo.clear()
            state_encoding_ipo = copy.deepcopy(state_encoding_i)
            state_encoding_i.clear()
        # the formula can now be accessed via state_encoding_ipo[0]
        self.solver.add(state_encoding_ipo[0])

        common.colourinfo("Encoded state quantifiers", False)

    def checkResult(self):
        starting_time = time.perf_counter()
        f = open("solver1.txt", "w")
        f.write(self.solver.to_smt2().__str__())
        f.close()
        truth = self.solver.check()
        z3_time = time.perf_counter() - starting_time
        list_of_actions = None # todo change
        set_of_holds = set()
        if truth == sat:
            z3model = self.solver.model()
            list_of_actions = [None] * self.model.getNumberOfActions() # todo change?
            for li in z3model:
                if li.name()[0] == 'h':
                    parts = li.name().split("_")
                    if parts[-2] == '0' and z3model[li]:
                        take_this = True
                        for i in range(self.no_of_stutter_quantifier):
                            if parts[1+i][-2] != '0':
                                take_this = False
                        if take_this:
                            state_tuple_list = [parts[1+i][1] for i in range(self.no_of_stutter_quantifier)]
                            set_of_holds.add(tuple(state_tuple_list))
                elif li.name()[0] == 'a' and len(li.name()) == 3: # todo change?
                    list_of_actions[int(li.name()[2:])] = z3model[li]
            print(list_of_actions, set_of_holds)

        return truth, list_of_actions, set_of_holds, self.solver.statistics(), z3_time

    def printResult(self, smt_end_time, scheduler_quantifier):
        print("Number of subformulas: " + str(self.no_of_subformula))
        common.colourinfo("Checking...", False)
        truth, actions, holds, statistics, z3_time = self.checkResult()
        common.colourinfo("Finished checking!", False)

        if truth.r == 1:
            smt_result = True
        elif truth.r == -1:
            smt_result = False
        else:
            print("Result unknown. Solver fails to solve constraints.")

        if truth.r in [1, -1]:
            # todo dont distinguish output by scheduler_quantifier? since we have many alternating quantifiers
            if scheduler_quantifier == 'exists':
                if smt_result:
                    # todo somehow also output stutter-scheduler?
                    common.colouroutput("The property HOLDS!")
                    print("\nThe values of variables of a witness are:") #todo mention more explicity that list mustnt be exhaustive?
                    print("\nIf both actions are available at a state:")
                    for i in range(0, len(actions)):
                        common.colouroutput("Choose action " + str(i) + " with probability " + str(actions[i]), False)
                    print(
                        "\nThe following state variable assignments satisfy the property "
                        "(tuples ordered by stutter quantification):")  # todo order of quantification? order of stutterquant ??
                    print(
                        holds)  # for each assignment: state associated with first stutter-sched var is listed first, and so on
                else:
                    common.colourerror("The property DOES NOT hold!")
            elif scheduler_quantifier == 'forall':
                if smt_result:
                    common.colourerror("The property DOES NOT hold!")
                    print("\nThe values of variables of a counterexample are:")
                    print("\nIf both actions are available at a state:")
                    for i in range(0, len(actions)):
                        common.colouroutput("Choose action " + str(i) + " with probability " + str(actions[i]), False)
                    print(
                        "\nThe following state variable assignments do not satisfy the property (tuples ordered by stutter quantification):")  # todo order of quantification? order of stutterquant ??
                    print(
                        holds)  # for each assignment: state associated with first stutter-sched var is listed first, and so on
                else:
                    common.colouroutput("The property HOLDS!")
        common.colourinfo("\nTime to encode in seconds: " + str(round(smt_end_time, 2)), False)
        common.colourinfo("Time required by z3 in seconds: " + str(round(z3_time, 2)), False)
        common.colourinfo(
            "Number of variables: " +
            str(len(self.dictOfInts.keys()) + len(self.dictOfReals.keys()) + len(self.dictOfBools.keys())),
            False)
        common.colourinfo("Number of formula checked: " + str(self.no_of_subformula), False)
        common.colourinfo("z3 statistics:", False)
        common.colourinfo(str(statistics), False)

    def fetch_value(self, list_with_value, value):
        # assuming value is a tuple
        res = 0
        for i in range(0, len(value)):
            res += value[i] * pow(len(self.model.getListOfStates()), len(value) - i - 1)
        return list_with_value[res]
