import copy
import itertools

from lark import Tree
from z3 import And, Bool, Real, Int, Not, Or, Xor, RealVal, Implies


def extendWithoutDuplicates(list1, list2):
    result = []
    if list1 is not None:
        result.extend(list1)
    if list2 is not None:
        result.extend(x for x in list2 if x not in result)
    return result


class SemanticsEncoder:

    def __init__(self, model,
                 solver, list_of_subformula, list_of_bools, listOfBools, list_of_ints, listOfInts, no_of_subformula,
                 no_of_state_quantifier, no_of_stutter_quantifier, lengthOfStutter, stutter_state_mapping):
        self.model = model
        self.solver = solver
        self.list_of_subformula = list_of_subformula
        self.list_of_reals = []
        self.listOfReals = []
        self.list_of_bools = list_of_bools
        self.listOfBools = listOfBools
        self.list_of_ints = list_of_ints
        self.listOfInts = listOfInts
        self.no_of_subformula = no_of_subformula
        self.no_of_state_quantifier = no_of_state_quantifier
        self.no_of_stutter_quantifier = no_of_stutter_quantifier
        self.stutterLength = lengthOfStutter  # default value 1 (no stutter)
        self.stutter_state_mapping = stutter_state_mapping

    def encodeSemantics(self, hyperproperty, prev_relevant_quantifier=[]):
        relevant_quantifier = []
        if len(prev_relevant_quantifier) > 0:
            relevant_quantifier.extend(prev_relevant_quantifier)

        if hyperproperty.data == 'true':
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            name = "holds"
            r_state = [(0, 0) for _ in range(self.no_of_stutter_quantifier)]
            for ind in r_state:
                name += "_" + str(ind)
            name += '_' + str(index_of_phi)
            self.addToVariableList(name)
            self.solver.add(self.listOfBools[self.list_of_bools.index(name)])
            self.no_of_subformula += 1
            return relevant_quantifier

        elif hyperproperty.data == 'atomic_proposition':
            ap_name = hyperproperty.children[0].children[0].value  # gets the name of the proposition
            proposition_relevant_stutter = int(
                hyperproperty.children[1].children[0].value[1])  # relevant stutter quantifier
            # TODO find relevant state
            # proposition_relevant_state = self.stutter_state_mapping[proposition_relevant_stutter-1]
            labeling = self.model.parsed_model.labeling
            if proposition_relevant_stutter not in relevant_quantifier:
                relevant_quantifier.append(proposition_relevant_stutter)
            and_for_yes = set()
            and_for_no = set()
            list_of_state_with_ap = []

            index_of_phi = self.list_of_subformula.index(hyperproperty)
            for state in self.model.getListOfStates():
                if ap_name in labeling.get_labels_of_state(state):
                    list_of_state_with_ap.append(state)
            combined_state_list = self.generateComposedStatesWithStutter(
                relevant_quantifier)  # tuples without stutterlength
            # combined_state_list_with_stutter = self.generateComposedStatesWithStutter(relevant_quantifier)
            for r_state in combined_state_list:
                name = 'holds'
                for tup in r_state:
                    name += '_' + str(tup)
                name += '_' + str(index_of_phi)
                self.addToVariableList(name)  # should look like: holds_(0, 0)_(0, 0)_2

                # check whether atomic proposition holds or not
                if r_state[proposition_relevant_stutter - 1][0] in list_of_state_with_ap:
                    and_for_yes.add(self.listOfBools[self.list_of_bools.index(name)])
                else:
                    and_for_no.add(Not(self.listOfBools[self.list_of_bools.index(name)]))
            self.solver.add(And(And([par for par in list(and_for_yes)]), And([par for par in list(and_for_no)])))
            self.no_of_subformula += 3
            and_for_yes.clear()
            and_for_no.clear()
            return relevant_quantifier
        elif hyperproperty.data == 'and':
            rel_quant1 = self.encodeSemantics(hyperproperty.children[0])
            rel_quant2 = self.encodeSemantics(hyperproperty.children[1])
            relevant_quantifier = extendWithoutDuplicates(rel_quant1, rel_quant2)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_of_phi1 = self.list_of_subformula.index(hyperproperty.children[0])
            index_of_phi2 = self.list_of_subformula.index(hyperproperty.children[1])
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'holds'
                for tup in r_state:
                    name1 += "_" + str(tup)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str((0, 0))
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str((0, 0))
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                first_and = And(self.listOfBools[self.list_of_bools.index(name1)],
                                self.listOfBools[self.list_of_bools.index(name2)],
                                self.listOfBools[self.list_of_bools.index(name3)])
                self.no_of_subformula += 1
                second_and = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 Or(Not(self.listOfBools[self.list_of_bools.index(name2)]),
                                    Not(self.listOfBools[self.list_of_bools.index(name3)])))
                self.no_of_subformula += 1
                self.solver.add(Or(first_and, second_and))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'or':
            rel_quant1 = self.encodeSemantics(hyperproperty.children[0])
            rel_quant2 = self.encodeSemantics(hyperproperty.children[1])
            relevant_quantifier = extendWithoutDuplicates(rel_quant1, rel_quant2)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_of_phi1 = self.list_of_subformula.index(hyperproperty.children[0])
            index_of_phi2 = self.list_of_subformula.index(hyperproperty.children[1])
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'holds'
                for tup in r_state:
                    name1 += "_" + str(tup)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str((0, 0))
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str((0, 0))
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                first_and = And(self.listOfBools[self.list_of_bools.index(name1)],
                                Or(self.listOfBools[self.list_of_bools.index(name2)],
                                   self.listOfBools[self.list_of_bools.index(name3)]))
                self.no_of_subformula += 1
                second_and = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 And(Not(self.listOfBools[self.list_of_bools.index(name2)]),
                                     Not(self.listOfBools[self.list_of_bools.index(name3)])))
                self.no_of_subformula += 1
                self.solver.add(Or(first_and, second_and))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'implies':
            rel_quant1 = self.encodeSemantics(hyperproperty.children[0])
            rel_quant2 = self.encodeSemantics(hyperproperty.children[1])
            relevant_quantifier = extendWithoutDuplicates(rel_quant1, rel_quant2)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_of_phi1 = self.list_of_subformula.index(hyperproperty.children[0])
            index_of_phi2 = self.list_of_subformula.index(hyperproperty.children[1])
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'holds'
                for tup in r_state:
                    name1 += "_" + str(tup)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str((0, 0))
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str((0, 0))
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                first_and = And(self.listOfBools[self.list_of_bools.index(name1)],
                                Or(Not(self.listOfBools[self.list_of_bools.index(name2)]),
                                   self.listOfBools[self.list_of_bools.index(name3)]))
                self.no_of_subformula += 1
                second_and = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 And(self.listOfBools[self.list_of_bools.index(name2)],
                                     Not(self.listOfBools[self.list_of_bools.index(name3)])))
                self.no_of_subformula += 1
                self.solver.add(Or(first_and, second_and))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'biconditional':
            rel_quant1 = self.encodeSemantics(hyperproperty.children[0])
            rel_quant2 = self.encodeSemantics(hyperproperty.children[1])
            relevant_quantifier = extendWithoutDuplicates(rel_quant1, rel_quant2)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_of_phi1 = self.list_of_subformula.index(hyperproperty.children[0])
            index_of_phi2 = self.list_of_subformula.index(hyperproperty.children[1])
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'holds'
                for tup in r_state:
                    name1 += "_" + str(tup)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str((0, 0))
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str((0, 0))
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                first_and = And(self.listOfBools[self.list_of_bools.index(name1)],
                                Or(
                                    And(self.listOfBools[self.list_of_bools.index(name2)],
                                        self.listOfBools[self.list_of_bools.index(name3)]),
                                    And(Not(self.listOfBools[self.list_of_bools.index(name2)]),
                                        Not(self.listOfBools[self.list_of_bools.index(name3)]))))
                self.no_of_subformula += 1
                second_and = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 Or(
                                     And(Not(self.listOfBools[self.list_of_bools.index(name2)]),
                                         self.listOfBools[self.list_of_bools.index(name3)]),
                                     And(self.listOfBools[self.list_of_bools.index(name2)],
                                         Not(self.listOfBools[self.list_of_bools.index(name3)]))))
                self.no_of_subformula += 1
                self.solver.add(Or(first_and, second_and))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'not':
            relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                          self.encodeSemantics(hyperproperty.children[0]))
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_of_phi1 = self.list_of_subformula.index(hyperproperty.children[0])

            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'holds'
                for tup in r_state:
                    name1 += "_" + str(tup)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'holds'
                for ind in r_state:
                    name2 += "_" + str(ind)
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                self.solver.add(Xor(self.listOfBools[self.list_of_bools.index(name1)],
                                    self.listOfBools[self.list_of_bools.index(name2)]))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'probability':
            child = hyperproperty.children[0]
            if child.data == 'next':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeNextSemantics(hyperproperty,
                                                                                       relevant_quantifier))
            elif child.data == 'until_unbounded':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeUnboundedUntilSemantics(hyperproperty,
                                                                                                 relevant_quantifier))
            elif child.data == 'until_bounded':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeBoundedUntilSemantics(hyperproperty,
                                                                                               relevant_quantifier)[0])
            elif child.data == 'future':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeFutureSemantics(hyperproperty,
                                                                                         relevant_quantifier))
            elif child.data == 'global':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeGlobalSemantics(hyperproperty,
                                                                                         relevant_quantifier))
            return relevant_quantifier

        elif hyperproperty.data == 'less_probability':
            rel_quant1 = self.encodeSemantics(hyperproperty.children[0])
            rel_quant2 = self.encodeSemantics(hyperproperty.children[1])
            relevant_quantifier = extendWithoutDuplicates(rel_quant1, rel_quant2)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_of_phi1 = self.list_of_subformula.index(hyperproperty.children[0])
            index_of_phi2 = self.list_of_subformula.index(hyperproperty.children[1])
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'holds'
                for tup in r_state:
                    name1 += "_" + str(tup)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str((0, 0))
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str((0, 0))
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] < self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] >= self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'equal_probability':
            rel_quant1 = self.encodeSemantics(hyperproperty.children[0])
            rel_quant2 = self.encodeSemantics(hyperproperty.children[1])
            relevant_quantifier = extendWithoutDuplicates(rel_quant1, rel_quant2)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_of_phi1 = self.list_of_subformula.index(hyperproperty.children[0])
            index_of_phi2 = self.list_of_subformula.index(hyperproperty.children[1])
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'holds'
                for tup in r_state:
                    name1 += "_" + str(tup)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str((0, 0))
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str((0, 0))
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] == self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] != self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'greater_probability':
            rel_quant1 = self.encodeSemantics(hyperproperty.children[0])
            rel_quant2 = self.encodeSemantics(hyperproperty.children[1])
            relevant_quantifier = extendWithoutDuplicates(rel_quant1, rel_quant2)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_of_phi1 = self.list_of_subformula.index(hyperproperty.children[0])
            index_of_phi2 = self.list_of_subformula.index(hyperproperty.children[1])
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'holds'
                for tup in r_state:
                    name1 += "_" + str(tup)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str((0, 0))
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str((0, 0))
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] > self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] <= self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'greater_and_equal_probability':
            rel_quant1 = self.encodeSemantics(hyperproperty.children[0])
            rel_quant2 = self.encodeSemantics(hyperproperty.children[1])
            relevant_quantifier = extendWithoutDuplicates(rel_quant1, rel_quant2)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_of_phi1 = self.list_of_subformula.index(hyperproperty.children[0])
            index_of_phi2 = self.list_of_subformula.index(hyperproperty.children[1])
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'holds'
                for tup in r_state:
                    name1 += "_" + str(tup)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str((0, 0))
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str((0, 0))
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] >= self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] < self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'less_and_equal_probability':
            rel_quant1 = self.encodeSemantics(hyperproperty.children[0])
            rel_quant2 = self.encodeSemantics(hyperproperty.children[1])
            relevant_quantifier = extendWithoutDuplicates(rel_quant1, rel_quant2)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_of_phi1 = self.list_of_subformula.index(hyperproperty.children[0])
            index_of_phi2 = self.list_of_subformula.index(hyperproperty.children[1])
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'holds'
                for tup in r_state:
                    name1 += "_" + str(tup)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str((0, 0))
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str((0, 0))
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] <= self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] > self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'constant_probability':
            constant = RealVal(hyperproperty.children[0].value).as_fraction().limit_denominator(10000)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            name = "prob"
            r_state = [(0, 0) for _ in range(self.no_of_stutter_quantifier)]
            for tup in r_state:
                name += "_" + str(tup)
            name += '_' + str(index_of_phi)
            self.addToVariableList(name)
            self.solver.add(self.listOfReals[self.list_of_reals.index(name)] == constant)
            self.no_of_subformula += 1
            return relevant_quantifier

        elif hyperproperty.data in ['add_probability', 'subtract_probability', 'multiply_probability']:
            rel_quant1 = self.encodeSemantics(hyperproperty.children[0])
            rel_quant2 = self.encodeSemantics(hyperproperty.children[1])
            relevant_quantifier = extendWithoutDuplicates(rel_quant1, rel_quant2)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_left = self.list_of_subformula.index(hyperproperty.children[0])
            index_right = self.list_of_subformula.index(hyperproperty.children[1])
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'prob'
                for tup in r_state:
                    name1 += "_" + str(tup)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str((0, 0))
                name2 += '_' + str(index_left)
                self.addToVariableList(name2)
                name3 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str((0, 0))
                name3 += '_' + str(index_right)
                self.addToVariableList(name3)
                if hyperproperty.data == 'add_probability':
                    self.solver.add(self.listOfReals[self.list_of_reals.index(name1)] == (
                            self.listOfReals[self.list_of_reals.index(name2)] + self.listOfReals[
                        self.list_of_reals.index(name3)]))
                    self.no_of_subformula += 2
                elif hyperproperty.data == 'subtract_probability':
                    self.solver.add(self.listOfReals[self.list_of_reals.index(name1)] == (
                            self.listOfReals[self.list_of_reals.index(name2)] - self.listOfReals[
                        self.list_of_reals.index(name3)]))
                    self.no_of_subformula += 2
                elif hyperproperty.data == 'multiply_probability':
                    self.solver.add(self.listOfReals[self.list_of_reals.index(name1)] == (
                            self.listOfReals[self.list_of_reals.index(name2)] * self.listOfReals[
                        self.list_of_reals.index(name3)]))
                    self.no_of_subformula += 2
                else:
                    print("Unexpected operator. Exiting")
                    return -1
            return relevant_quantifier

        else:
            self.encodeSemantics(hyperproperty.children[0])

    def addToVariableList(self, name):
        # TODO reuse nethod in modelchecker
        if name[0] == 'h' and not name.startswith('holdsToInt') and name not in self.list_of_bools:
            self.list_of_bools.append(name)
            self.listOfBools.append(Bool(name))
        elif (name[0] in ['p', 'd', 'r'] or name.startswith('holdsToInt')) and name not in self.list_of_reals:
            self.list_of_reals.append(name)
            self.listOfReals.append(Real(name))
        elif name[0] in ['a', 't'] and name not in self.list_of_ints:
            self.list_of_ints.append(name)
            self.listOfInts.append(Int(name))

    def generateComposedStatesWithStutter(self, list_of_relevant_quantifier):
        """
        Generates combination of states based on relevant quantifiers
        :param list_of_relevant_quantifier: ranges from value 1- (no. of quantifiers)
        :return: list of composed states.
        """
        states_with_stuttering = list(
            itertools.product(self.model.getListOfStates(), list(range(self.stutterLength))))

        stored_list = []
        for quant in range(1, self.no_of_state_quantifier + 1):
            if quant in list_of_relevant_quantifier:
                stored_list.append(states_with_stuttering)
            else:
                stored_list.append([(0, 0)])
        return list(itertools.product(*stored_list))

    def generateComposedStates(self, list_of_relevant_quantifier):
        """
        Generates combination of states based on relevant quantifiers
        :param list_of_relevant_quantifier: ranges from value 1- (no. of quantifiers)
        :return: list of composed states.
        """
        stored_list = []
        for quant in range(1, self.no_of_state_quantifier + 1):
            if quant in list_of_relevant_quantifier:
                stored_list.append(self.model.getListOfStates())
            else:
                stored_list.append([0])
        return list(itertools.product(*stored_list))

    def encodeNextSemantics(self, hyperproperty, prev_relevant_quantifier=[]):
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        relevant_quantifier = self.encodeSemantics(phi1, prev_relevant_quantifier)
        combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)

        for r_state in combined_state_list:
            holds1 = 'holds'
            str_r_state = ""
            for tup in r_state:
                str_r_state += "_" + str(tup)
            holds1 += str_r_state + "_" + str(index_of_phi1)
            self.addToVariableList(holds1)
            holdsToInt1 = 'holdsToInt' + str_r_state + "_" + str(index_of_phi1)
            self.addToVariableList(holdsToInt1)
            prob_phi = 'prob' + str_r_state + "_" + str(index_of_phi)
            self.addToVariableList(prob_phi)
            first_and = Or(
                And(self.listOfReals[self.list_of_reals.index(holdsToInt1)] == float(1),
                    self.listOfBools[self.list_of_bools.index(holds1)]),
                And(self.listOfReals[self.list_of_reals.index(holdsToInt1)] == float(0),
                    Not(self.listOfBools[self.list_of_bools.index(holds1)])))
            self.no_of_subformula += 3
            self.solver.add(first_and)

            dicts_act = []
            dicts_stutter = []
            for l in relevant_quantifier:
                dicts_act.append(self.model.dict_of_acts[r_state[l - 1][0]])
                dicts_stutter.append(list(range(r_state[l-1][1],self.stutterLength)))
            combined_acts = list(itertools.product(*dicts_act))
            combined_stutters = list(itertools.product(*dicts_stutter))

            for ca in combined_acts:
                for h_tuple in combined_stutters:
                    act_stu_str_list = []
                    for l in range(len(relevant_quantifier)):
                        name = 'a_' + str(r_state[relevant_quantifier[l] - 1][0])
                        self.addToVariableList(name)
                        stu_name = 't_' + str(relevant_quantifier[l]) + '_' + str(
                            r_state[relevant_quantifier[l] - 1][0])
                        self.addToVariableList(stu_name)
                        act_stu_str_list.append(self.listOfInts[self.list_of_ints.index(name)] == int(ca[l]))
                        act_stu_str_list.append(self.listOfInts[self.list_of_ints.index(stu_name)] == int(h_tuple[l]))
                    implies_precedent = And(act_stu_str_list)
                    self.no_of_subformula += 1

                    combined_succ = self.genSuccessors(r_state, ca, h_tuple, relevant_quantifier)
                    sum_left = RealVal(0).as_fraction()

                    for cs in combined_succ:
                        holdsToInt_succ = 'holdsToInt'
                        prod_left_part = RealVal(1).as_fraction()
                        for l in range(1, self.no_of_stutter_quantifier + 1):
                            if l in relevant_quantifier:
                                succ_state = cs[relevant_quantifier.index(l)][0]
                                holdsToInt_succ += '_' + succ_state
                                prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                            else:
                                holdsToInt_succ += '_' + str((0, 0))

                        holdsToInt_succ += '_' + str(index_of_phi1)
                        self.addToVariableList(holdsToInt_succ)
                        prod_left_part *= self.listOfReals[self.list_of_reals.index(holdsToInt_succ)]

                        sum_left += prod_left_part
                        self.no_of_subformula += 1

                    implies_antecedent_and = self.listOfReals[self.list_of_reals.index(prob_phi)] == sum_left
                    self.no_of_subformula += 1
                    self.solver.add(Implies(implies_precedent, implies_antecedent_and))
                    self.no_of_subformula += 1

        return relevant_quantifier

    def genSuccessors(self, r_state, ca, h_tuple, relevant_quantifier):
        dicts = []
        for l in range(len(relevant_quantifier)):
            if h_tuple[l] == r_state[l][1]:
                succ = (
                    self.model.dict_of_acts_tran[str(r_state[l][0]) + " " + str(ca[l])])
                list_of_all_succ = []
                for s in succ:
                    space = s.find(' ')
                    succ_state = (int(s[0:space]), 0)
                    list_of_all_succ.append([str(succ_state), s[space + 1:]])
            else: # if r_state[l][1] < h_tuple[l]
                list_of_all_succ = [[str((r_state[l][0], r_state[l][1] + 1)), str(1)]]
            dicts.append(list_of_all_succ)
        return list(itertools.product(*dicts))

    def encodeUnboundedUntilSemantics(self, hyperproperty, relevant_quantifier=[]):
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        rel_quant1 = self.encodeSemantics(phi1)
        relevant_quantifier = extendWithoutDuplicates(rel_quant1, relevant_quantifier)
        phi2 = hyperproperty.children[0].children[1]
        index_of_phi2 = self.list_of_subformula.index(phi2)
        rel_quant2 = self.encodeSemantics(phi2)
        relevant_quantifier = extendWithoutDuplicates(rel_quant2, relevant_quantifier)
        combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)

        for r_state in combined_state_list:
            holds1 = 'holds'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant1:
                    holds1 += "_" + str(r_state[ind])
                else:
                    holds1 += "_" + str((0, 0))
            holds1 += "_" + str(index_of_phi1)
            self.addToVariableList(holds1)
            holds2 = 'holds'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant2:
                    holds2 += "_" + str(r_state[ind])
                else:
                    holds2 += "_" + str((0, 0))
            holds2 += "_" + str(index_of_phi2)
            self.addToVariableList(holds2)
            prob_phi = 'prob'
            for tup in r_state:
                prob_phi += "_" + str(tup)
            prob_phi += '_' + str(index_of_phi)
            self.addToVariableList(prob_phi)
            new_prob_const_0 = self.listOfReals[self.list_of_reals.index(prob_phi)] >= float(0)
            new_prob_const_1 = self.listOfReals[self.list_of_reals.index(prob_phi)] <= float(1)
            first_implies = And(Implies(self.listOfBools[self.list_of_bools.index(holds2)],
                                        (self.listOfReals[self.list_of_reals.index(prob_phi)] == float(1))),
                                Implies(And(Not(self.listOfBools[self.list_of_bools.index(holds1)]),
                                            Not(self.listOfBools[self.list_of_bools.index(holds2)])),
                                        (self.listOfReals[self.list_of_reals.index(prob_phi)] == float(0))),
                                new_prob_const_0,
                                new_prob_const_1)
            self.solver.add(first_implies)
            self.no_of_subformula += 4

            dicts_act = []
            dicts_stutter = []
            for l in relevant_quantifier:
                dicts_act.append(self.model.dict_of_acts[r_state[l - 1][0]])
                dicts_stutter.append(list(range(r_state[l-1][1],self.stutterLength)))
            combined_acts = list(itertools.product(*dicts_act))
            combined_stutters = list(itertools.product(*dicts_stutter))

            for ca in combined_acts:
                for h_tuple in combined_stutters:
                    act_stu_str_list = []
                    for l in range(len(relevant_quantifier)):
                        name = 'a_' + str(r_state[relevant_quantifier[l] - 1][0])
                        self.addToVariableList(name)
                        stu_name = 't_' + str(relevant_quantifier[l]) + '_' + str(
                            r_state[relevant_quantifier[l] - 1][0])
                        self.addToVariableList(stu_name)
                        act_stu_str_list.append(self.listOfInts[self.list_of_ints.index(name)] == int(ca[l]))
                        act_stu_str_list.append(self.listOfInts[self.list_of_ints.index(stu_name)] == int(h_tuple[l]))
                    implies_precedent = And(self.listOfBools[self.list_of_bools.index(holds1)],
                                            Not(self.listOfBools[self.list_of_bools.index(holds2)]),
                                            And(act_stu_str_list))
                    self.no_of_subformula += 2

                    combined_succ = self.genSuccessors(r_state, ca, h_tuple, relevant_quantifier)
                    sum_left = RealVal(0).as_fraction()
                    list_of_ors = []

                    for cs in combined_succ:
                        prob_succ = 'prob'
                        holds_succ = 'holds'
                        d_current = 'd'
                        d_succ = 'd'
                        prod_left_part = RealVal(1).as_fraction()
                        for l in range(1, self.no_of_state_quantifier + 1):
                            if l in relevant_quantifier:
                                succ_state = cs[relevant_quantifier.index(l)][0]
                                prob_succ += '_' + succ_state
                                holds_succ += '_' + succ_state
                                d_succ += '_' + succ_state
                                prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                            else:
                                prob_succ += '_' + str((0, 0))
                                holds_succ += '_' + str((0, 0))
                                d_succ += '_' + str((0, 0))
                            d_current += '_' + str(r_state[l - 1])

                        prob_succ += '_' + str(index_of_phi)
                        self.addToVariableList(prob_succ)
                        holds_succ += '_' + str(index_of_phi2)
                        self.addToVariableList(holds_succ)

                        d_current += '_' + str(index_of_phi2)
                        self.addToVariableList(d_current)
                        d_succ += '_' + str(index_of_phi2)
                        self.addToVariableList(d_succ)
                        prod_left_part *= self.listOfReals[self.list_of_reals.index(prob_succ)]

                        sum_left += prod_left_part
                        self.no_of_subformula += 1

                        list_of_ors.append(Or(self.listOfBools[self.list_of_bools.index(holds_succ)],
                                              self.listOfReals[self.list_of_reals.index(d_current)] > self.listOfReals[
                                                  self.list_of_reals.index(d_succ)]))

                        self.no_of_subformula += 2

                    implies_antecedent_and1 = self.listOfReals[self.list_of_reals.index(prob_phi)] == sum_left
                    self.no_of_subformula += 1
                    prod_right_or = Or(list_of_ors)
                    self.no_of_subformula += 1
                    implies_antecedent_and2 = Implies(self.listOfReals[self.list_of_reals.index(prob_phi)] > 0,
                                                      prod_right_or)
                    self.no_of_subformula += 1
                    implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
                    self.no_of_subformula += 1
                    self.solver.add(Implies(implies_precedent, implies_antecedent))
                    self.no_of_subformula += 1

        return relevant_quantifier

    def encodeBoundedUntilSemantics(self, hyperproperty, relevant_quantifier=[]):
        k1 = int(hyperproperty.children[0].children[1].value)
        k2 = int(hyperproperty.children[0].children[2].value)

        index_of_phi = self.list_of_subformula.index(hyperproperty)
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        phi2 = hyperproperty.children[0].children[3]
        index_of_phi2 = self.list_of_subformula.index(phi2)

        if k2 == 0:
            rel_quant1 = self.encodeSemantics(phi1)
            relevant_quantifier = extendWithoutDuplicates(relevant_quantifier, rel_quant1)
            rel_quant2 = self.encodeSemantics(phi2)
            relevant_quantifier = extendWithoutDuplicates(relevant_quantifier, rel_quant2)
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)

            for r_state in combined_state_list:
                name1 = 'prob'
                for tup in r_state:
                    name1 += "_" + str(tup)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str((0, 0))
                name2 += '_' + str(index_of_phi2)
                self.addToVariableList(name2)

                eq1 = Implies(self.listOfBools[self.list_of_bools.index(name2)],
                              self.listOfReals[self.list_of_reals.index(name1)] == float(1))
                eq2 = Implies(Not(self.listOfBools[self.list_of_bools.index(name2)]),
                              self.listOfReals[self.list_of_reals.index(name1)] == float(0))
                self.no_of_subformula += 2
                self.solver.add(And(eq1, eq2))
                self.no_of_subformula += 1

        elif k1 == 0:
            left, k_1, k_2, right = hyperproperty.children[0].children
            par = copy.deepcopy(k_2)
            par.value = str(int(k_2.value) - 1)  # k2.value will have changed value but it won't show up in the formula
            # tree, hence it'll appear to be the same formula as formula_duplicate
            hyperproperty.children[0].children[
                2] = par  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2. Don't be confused!!
            self.list_of_subformula.append(hyperproperty)
            index_of_replaced = len(
                self.list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
            rel_quant, rel_quant1, rel_quant2 = self.encodeBoundedUntilSemantics(hyperproperty)
            relevant_quantifier = extendWithoutDuplicates(relevant_quantifier, rel_quant)
            # TODO isnt it unnecessary to add them again since we already added the quantifiers in the base case
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            # rel_quant1 = int(str(hyperproperty.children[0].children[0].children[1].children[0])[1:])
            # rel_quant2 = int(str(hyperproperty.children[0].children[3].children[1].children[0])[1:])

            for r_state in combined_state_list:
                holds1 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        holds1 += "_" + str(r_state[ind])
                    else:
                        holds1 += "_" + str((0, 0))
                holds1 += "_" + str(index_of_phi1)
                self.addToVariableList(holds1)
                holds2 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        holds2 += "_" + str(r_state[ind])
                    else:
                        holds2 += "_" + str((0, 0))
                holds2 += "_" + str(index_of_phi2)
                self.addToVariableList(holds2)
                prob_phi = 'prob'
                for tup in r_state:
                    prob_phi += "_" + str(tup)
                prob_phi += '_' + str(index_of_phi)
                self.addToVariableList(prob_phi)

                new_prob_const = self.listOfReals[self.list_of_reals.index(prob_phi)] >= float(0)
                # todo also require <= 1 ?
                first_implies = And(Implies(self.listOfBools[self.list_of_bools.index(holds2)],
                                            (self.listOfReals[self.list_of_reals.index(prob_phi)] == float(1))),
                                    Implies(And(Not(self.listOfBools[self.list_of_bools.index(holds1)]),
                                                Not(self.listOfBools[self.list_of_bools.index(holds2)])),
                                            (self.listOfReals[self.list_of_reals.index(prob_phi)] == float(0))),
                                    new_prob_const)
                self.no_of_subformula += 3
                self.solver.add(first_implies)

                dicts_act = []
                dicts_stutter = []
                for l in relevant_quantifier:
                    dicts_act.append(self.model.dict_of_acts[r_state[l - 1][0]])
                    dicts_stutter.append(list(range(r_state[l-1][1],self.stutterLength)))
                combined_acts = list(itertools.product(*dicts_act))
                combined_stutters = list(itertools.product(*dicts_stutter))

                for ca in combined_acts:
                    for h_tuple in combined_stutters:
                        act_stu_str_list = []
                        for l in range(len(relevant_quantifier)):
                            name = 'a_' + str(r_state[relevant_quantifier[0] - 1])
                            self.addToVariableList(name)
                            stu_name = 't_' + str(relevant_quantifier[l]) + '_' + str(
                                r_state[relevant_quantifier[l] - 1][0])
                            self.addToVariableList(stu_name)
                            act_stu_str_list.append(self.listOfInts[self.list_of_ints.index(name)] == int(ca[l]))
                            act_stu_str_list.append(
                                self.listOfInts[self.list_of_ints.index(stu_name)] == int(h_tuple[l]))
                        implies_precedent = And(self.listOfBools[self.list_of_bools.index(holds1)],
                                                Not(self.listOfBools[self.list_of_bools.index(holds2)]),
                                                And(act_stu_str_list))
                        self.no_of_subformula += 2

                        combined_succ = self.genSuccessors(r_state, ca, h_tuple, relevant_quantifier)
                        sum_left = RealVal(0).as_fraction()

                        for cs in combined_succ:
                            prob_succ = 'prob'
                            prod_left_part = RealVal(1).as_fraction()
                            for l in range(1, self.no_of_state_quantifier + 1):
                                if l in relevant_quantifier:
                                    succ_state = cs[relevant_quantifier.index(l)][0]
                                    prob_succ += '_' + succ_state
                                    prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                                else:
                                    prob_succ += '_' + str((0, 0))

                            prob_succ += '_' + str(index_of_replaced)
                            self.addToVariableList(prob_succ)
                            prod_left_part *= self.listOfReals[self.list_of_reals.index(prob_succ)]

                            sum_left += prod_left_part
                            self.no_of_subformula += 1

                        implies_antecedent_and = self.listOfReals[self.list_of_reals.index(prob_phi)] == sum_left
                        self.no_of_subformula += 1
                        self.solver.add(Implies(implies_precedent, implies_antecedent_and))
                        self.no_of_subformula += 1

        elif k1 > 0:
            left, k_1, k_2, right = hyperproperty.children[0].children
            par1 = copy.deepcopy(k_1)
            par2 = copy.deepcopy(k_2)
            par1.value = str(int(k_1.value) - 1)
            par2.value = str(int(k_2.value) - 1)
            hyperproperty.children[0].children[
                1] = par1  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2 Don't be confused!!
            hyperproperty.children[0].children[2] = par2
            self.list_of_subformula.append(hyperproperty)
            index_of_replaced = len(
                self.list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
            rel_quant, rel_quant1, rel_quant2 = self.encodeBoundedUntilSemantics(hyperproperty)
            relevant_quantifier = extendWithoutDuplicates(relevant_quantifier, rel_quant)
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            # rel_quant1 = int(str(hyperproperty.children[0].children[0].children[1].children[0])[1:])
            # rel_quant2 = int(str(hyperproperty.children[0].children[3].children[1].children[0])[1:])

            for r_state in combined_state_list:
                holds1 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) == rel_quant1:
                        holds1 += "_" + str(r_state[ind])
                    else:
                        holds1 += "_" + str((0, 0))
                holds1 += "_" + str(index_of_phi1)
                self.addToVariableList(holds1)
                prob_phi = 'prob'
                for tup in r_state:
                    prob_phi += "_" + str(tup)
                prob_phi += '_' + str(index_of_phi)
                self.addToVariableList(prob_phi)

                # todo also require >=0 and <=1 ?
                first_implies = Implies(Not(self.listOfBools[self.list_of_bools.index(holds1)]),
                                        (self.listOfReals[self.list_of_reals.index(prob_phi)] == float(0)))
                self.no_of_subformula += 1
                self.solver.add(first_implies)

                dicts_act = []
                dicts_stutter = []
                for l in relevant_quantifier:
                    dicts_act.append(self.model.dict_of_acts[r_state[l - 1][0]])
                    dicts_stutter.append(list(range(r_state[l-1][1],self.stutterLength)))
                combined_acts = list(itertools.product(*dicts_act))
                combined_stutters = list(itertools.product(*dicts_stutter))

                for ca in combined_acts:
                    for h_tuple in combined_stutters:
                        act_stu_str_list = []
                        for l in range(len(relevant_quantifier)):
                            name = 'a_' + str(r_state[relevant_quantifier[l] - 1][0])
                            self.addToVariableList(name)
                            stu_name = 't_' + str(relevant_quantifier[l]) + '_' + str(
                                r_state[relevant_quantifier[l] - 1][0])
                            self.addToVariableList(stu_name)
                            act_stu_str_list.append(self.listOfInts[self.list_of_ints.index(name)] == int(ca[l]))
                            act_stu_str_list.append(
                                self.listOfInts[self.list_of_ints.index(stu_name)] == int(h_tuple[l]))
                        implies_precedent = And(self.listOfBools[self.list_of_bools.index(holds1)],
                                                And(act_stu_str_list))
                        self.no_of_subformula += 2

                        combined_succ = self.genSuccessors(r_state, ca, h_tuple, relevant_quantifier)
                        sum_left = RealVal(0).as_fraction()

                        for cs in combined_succ:
                            prob_succ = 'prob'
                            prod_left_part = RealVal(1).as_fraction()
                            for l in range(1, self.no_of_state_quantifier + 1):
                                if l in relevant_quantifier:
                                    succ_state = cs[relevant_quantifier.index(l)][0]
                                    prob_succ += '_' + succ_state
                                    prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                                else:
                                    prob_succ += '_' + str((0, 0))

                            prob_succ += '_' + str(index_of_replaced)
                            self.addToVariableList(prob_succ)
                            prod_left_part *= self.listOfReals[self.list_of_reals.index(prob_succ)]

                            prod_left_part *= self.listOfReals[self.list_of_reals.index(prob_succ)]
                            sum_left += prod_left_part
                            self.no_of_subformula += 1

                        implies_antecedent_and = self.listOfReals[self.list_of_reals.index(prob_phi)] == sum_left
                        self.no_of_subformula += 1
                        self.solver.add(Implies(implies_precedent, implies_antecedent_and))
                        self.no_of_subformula += 1
        return relevant_quantifier, rel_quant1, rel_quant2

    def encodeFutureSemantics(self, hyperproperty, relevant_quantifier=[]):
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        rel_quant = self.encodeSemantics(phi1)
        relevant_quantifier = extendWithoutDuplicates(relevant_quantifier, rel_quant)
        combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)

        for r_state in combined_state_list:
            holds1 = 'holds'
            str_r_state = ""
            for ind in r_state:
                str_r_state += "_" + str(ind)
            holds1 += str_r_state + "_" + str(index_of_phi1)
            self.addToVariableList(holds1)
            prob_phi = 'prob'
            prob_phi += str_r_state + '_' + str(index_of_phi)
            self.addToVariableList(prob_phi)
            new_prob_const_0 = self.listOfReals[self.list_of_reals.index(prob_phi)] >= float(0)
            new_prob_const_1 = self.listOfReals[self.list_of_reals.index(prob_phi)] <= float(1)
            first_implies = And(Implies(self.listOfBools[self.list_of_bools.index(holds1)],
                                        (self.listOfReals[self.list_of_reals.index(prob_phi)] == float(1))),
                                new_prob_const_0,
                                new_prob_const_1)
            self.solver.add(first_implies)
            self.no_of_subformula += 3

            dicts_act = []
            dicts_stutter = []
            for l in relevant_quantifier:
                dicts_act.append(self.model.dict_of_acts[r_state[l - 1][0]])
                dicts_stutter.append(list(range(r_state[l-1][1],self.stutterLength)))
            combined_acts = list(itertools.product(*dicts_act))
            combined_stutters = list(itertools.product(*dicts_stutter))

            for ca in combined_acts:
                for h_tuple in combined_stutters:
                    act_stu_str_list = []
                    for l in range(len(relevant_quantifier)):
                        name = 'a_' + str(r_state[relevant_quantifier[l] - 1][0])
                        self.addToVariableList(name)
                        stu_name = 't_' + str(relevant_quantifier[l]) + '_' + str(
                            r_state[relevant_quantifier[l] - 1][0])
                        self.addToVariableList(stu_name)
                        act_stu_str_list.append(self.listOfInts[self.list_of_ints.index(name)] == int(ca[l]))
                        act_stu_str_list.append(self.listOfInts[self.list_of_ints.index(stu_name)] == int(h_tuple[l]))
                    implies_precedent = And(Not(self.listOfBools[self.list_of_bools.index(holds1)]),
                                            And(act_stu_str_list))
                    self.no_of_subformula += 2

                    combined_succ = self.genSuccessors(r_state, ca, h_tuple, relevant_quantifier)
                    sum_left = RealVal(0).as_fraction()
                    list_of_ors = []

                    for cs in combined_succ:
                        prob_succ = 'prob'
                        holds_succ = 'holds'
                        d_current = 'd'
                        d_succ = 'd'
                        prod_left_part = RealVal(1).as_fraction()
                        for l in range(1, self.no_of_state_quantifier + 1):
                            if l in relevant_quantifier:
                                succ_state = cs[relevant_quantifier.index(l)][0]
                                prob_succ += '_' + succ_state
                                holds_succ += '_' + succ_state
                                d_succ += '_' + succ_state
                                prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                            else:
                                prob_succ += '_' + str((0, 0))
                                holds_succ += '_' + str((0, 0))
                                d_succ += '_' + str((0, 0))
                            d_current += '_' + str(r_state[l - 1])

                        prob_succ += '_' + str(index_of_phi)
                        self.addToVariableList(prob_succ)
                        holds_succ += '_' + str(index_of_phi1)
                        self.addToVariableList(holds_succ)
                        d_current += '_' + str(index_of_phi1)
                        self.addToVariableList(d_current)
                        d_succ += '_' + str(index_of_phi1)
                        self.addToVariableList(d_succ)
                        prod_left_part *= self.listOfReals[self.list_of_reals.index(prob_succ)]

                        sum_left += prod_left_part
                        self.no_of_subformula += 1

                        list_of_ors.append(Or(self.listOfBools[self.list_of_bools.index(holds_succ)],
                                              self.listOfReals[self.list_of_reals.index(d_current)] > self.listOfReals[
                                                  self.list_of_reals.index(d_succ)]))

                        self.no_of_subformula += 2

                    implies_antecedent_and1 = self.listOfReals[self.list_of_reals.index(prob_phi)] == sum_left
                    self.no_of_subformula += 1
                    prod_right_or = Or(list_of_ors)
                    self.no_of_subformula += 1
                    implies_antecedent_and2 = Implies(self.listOfReals[self.list_of_reals.index(prob_phi)] > 0,
                                                      prod_right_or)
                    self.no_of_subformula += 1
                    implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
                    self.no_of_subformula += 1
                    self.solver.add(Implies(implies_precedent, implies_antecedent))
                    self.no_of_subformula += 1
        return relevant_quantifier

    def encodeGlobalSemantics(self, hyperproperty, relevant_quantifier=[]):
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        rel_quant1 = self.encodeSemantics(phi1)
        relevant_quantifier = extendWithoutDuplicates(rel_quant1, relevant_quantifier)
        combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)

        for r_state in combined_state_list:
            holds1 = 'holds'
            str_r_state = ""
            for tup in r_state:
                str_r_state += "_" + str(tup)
            holds1 += str_r_state + "_" + str(index_of_phi1)
            self.addToVariableList(holds1)
            prob_phi = 'prob'
            prob_phi += str_r_state + '_' + str(index_of_phi)
            self.addToVariableList(prob_phi)
            new_prob_const_0 = self.listOfReals[self.list_of_reals.index(prob_phi)] >= float(0)
            new_prob_const_1 = self.listOfReals[self.list_of_reals.index(prob_phi)] <= float(1)
            first_implies = And(Implies((Not(self.listOfBools[self.list_of_bools.index(holds1)])),
                                        (self.listOfReals[self.list_of_reals.index(prob_phi)] == float(0))),
                                new_prob_const_0,
                                new_prob_const_1)
            self.solver.add(first_implies)
            self.no_of_subformula += 1

            dicts_act = []
            dicts_stutter = []
            for l in relevant_quantifier:
                dicts_act.append(self.model.dict_of_acts[r_state[l - 1][0]])
                dicts_stutter.append(list(range(r_state[l-1][1],self.stutterLength))) # only consider stutterlength, with which the current state is reachable
            combined_acts = list(itertools.product(*dicts_act))
            combined_stutters = list(itertools.product(*dicts_stutter))

            for ca in combined_acts:
                for h_tuple in combined_stutters:
                    act_stu_str_list = []
                    for l in range(len(relevant_quantifier)):
                        name = 'a_' + str(r_state[relevant_quantifier[l] - 1][0])
                        self.addToVariableList(name)
                        stu_name = 't_' + str(relevant_quantifier[l]) + '_' + str(
                            r_state[relevant_quantifier[l] - 1][0])
                        self.addToVariableList(stu_name)
                        act_stu_str_list.append(self.listOfInts[self.list_of_ints.index(name)] == int(ca[l]))
                        act_stu_str_list.append(self.listOfInts[self.list_of_ints.index(stu_name)] == int(h_tuple[l]))
                    implies_precedent = And(self.listOfBools[self.list_of_bools.index(holds1)],
                                            And(act_stu_str_list))
                    self.no_of_subformula += 2

                    combined_succ = self.genSuccessors(r_state, ca, h_tuple, relevant_quantifier)
                    sum_left = RealVal(0).as_fraction()
                    list_of_ors = []

                    for cs in combined_succ:
                        prob_succ = 'prob'
                        holds_succ = 'holds'
                        d_current = 'd'
                        d_succ = 'd'
                        prod_left_part = RealVal(1).as_fraction()
                        for l in range(1, self.no_of_state_quantifier + 1):
                            if l in relevant_quantifier:
                                succ_state = cs[relevant_quantifier.index(l)][0]
                                prob_succ += '_' + succ_state
                                holds_succ += '_' + succ_state
                                d_succ += '_' + succ_state
                                prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                            else:
                                prob_succ += '_' + str((0, 0))
                                holds_succ += '_' + str((0, 0))
                                d_succ += '_' + str((0, 0))
                            d_current += '_' + str(r_state[l - 1])

                        prob_succ += '_' + str(index_of_phi)
                        self.addToVariableList(prob_succ)

                        prod_left_part *= self.listOfReals[self.list_of_reals.index(prob_succ)]
                        sum_left += prod_left_part
                        self.no_of_subformula += 1

                        # loop condition
                        holds_succ += '_' + str(index_of_phi1)
                        self.addToVariableList(holds_succ)
                        d_current += '_' + str(index_of_phi1)
                        self.addToVariableList(d_current)
                        d_succ += '_' + str(index_of_phi1)
                        self.addToVariableList(d_succ)

                        list_of_ors.append(Or(Not(self.listOfBools[self.list_of_bools.index(holds_succ)]),
                                              self.listOfReals[self.list_of_reals.index(d_current)] > self.listOfReals[
                                                  self.list_of_reals.index(d_succ)]))
                        self.no_of_subformula += 2

                    implies_antecedent_and1 = self.listOfReals[self.list_of_reals.index(prob_phi)] == sum_left
                    self.no_of_subformula += 1

                    prod_right_or = Or(list_of_ors)
                    self.no_of_subformula += 1
                    implies_antecedent_and2 = Implies(self.listOfReals[self.list_of_reals.index(prob_phi)] < 1,
                                                      prod_right_or)
                    self.no_of_subformula += 1
                    implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
                    self.no_of_subformula += 1
                    self.solver.add(Implies(implies_precedent, implies_antecedent))
                    self.no_of_subformula += 1

        return relevant_quantifier
