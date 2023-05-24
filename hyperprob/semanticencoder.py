import copy
import itertools

from z3 import And, Bool, Real, Not, Or, Xor, RealVal, Implies, Product, Sum

def extendWithoutDuplicates(list1, list2):
    result = []
    if list1 is not None:
        result.extend(list1)
    if list2 is not None:
        result.extend(x for x in list2 if x not in result)
    return result


class SemanticsEncoder:

    def __init__(self, model,
                 solver, list_of_subformula, dictOfReals, dictOfBools,
                 no_of_subformula, no_of_state_quantifier, no_of_stutter_quantifier, lengthOfStutter,
                 stutter_state_mapping):
        self.model = model
        self.solver = solver
        self.list_of_subformula = list_of_subformula
        self.dictOfReals = dictOfReals
        self.dictOfBools = dictOfBools
        self.no_of_subformula = no_of_subformula
        self.no_of_state_quantifier = no_of_state_quantifier
        self.no_of_stutter_quantifier = no_of_stutter_quantifier
        self.stutterLength = lengthOfStutter  # default value 1 (no stutter)
        self.stutter_state_mapping = stutter_state_mapping

    def encodeSemantics(self, hyperproperty, prev_relevant_quantifier=[]):
        """
        Main method for semantic encoding
        :param hyperproperty: non-quantified A-HyperProb property
        :param prev_relevant_quantifier: previously relevant quantifiers
        :return: relevant_quantifier: list of quantifiers relevant for the the hyperproperty
        """
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
            self.solver.add(self.dictOfBools[name])
            self.no_of_subformula += 1
            return relevant_quantifier

        elif hyperproperty.data == 'atomic_proposition':
            ap_name = hyperproperty.children[0].children[0].value  # gets the name of the proposition
            proposition_relevant_stutter = int(
                hyperproperty.children[1].children[0].value[1])  # relevant stutter quantifier
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
            combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)
            for r_state in combined_state_list:
                name = 'holds'
                for tup in r_state:
                    name += '_' + str(tup)
                name += '_' + str(index_of_phi)
                self.addToVariableList(name)  # should look like: holds_(0, 0)_(0, 0)_2

                # check whether atomic proposition holds or not
                if r_state[proposition_relevant_stutter - 1][0] in list_of_state_with_ap:
                    and_for_yes.add(self.dictOfBools[name])
                else:
                    and_for_no.add(Not(self.dictOfBools[name]))
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
                first_and = And(self.dictOfBools[name1],
                                self.dictOfBools[name2],
                                self.dictOfBools[name3])
                self.no_of_subformula += 1
                second_and = And(Not(self.dictOfBools[name1]),
                                 Or(Not(self.dictOfBools[name2]),
                                    Not(self.dictOfBools[name3])))
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
                first_and = And(self.dictOfBools[name1],
                                Or(self.dictOfBools[name2],
                                   self.dictOfBools[name3]))
                self.no_of_subformula += 1
                second_and = And(Not(self.dictOfBools[name1]),
                                 And(Not(self.dictOfBools[name2]),
                                     Not(self.dictOfBools[name3])))
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
                first_and = And(self.dictOfBools[name1],
                                Or(Not(self.dictOfBools[name2]),
                                   self.dictOfBools[name3]))
                self.no_of_subformula += 1
                second_and = And(Not(self.dictOfBools[name1]),
                                 And(self.dictOfBools[name2],
                                     Not(self.dictOfBools[name3])))
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
                first_and = And(self.dictOfBools[name1],
                                Or(
                                    And(self.dictOfBools[name2],
                                        self.dictOfBools[name3]),
                                    And(Not(self.dictOfBools[name2]),
                                        Not(self.dictOfBools[name3]))))
                self.no_of_subformula += 1
                second_and = And(Not(self.dictOfBools[name1]),
                                 Or(
                                     And(Not(self.dictOfBools[name2]),
                                         self.dictOfBools[name3]),
                                     And(self.dictOfBools[name2],
                                         Not(self.dictOfBools[name3]))))
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
                self.solver.add(Xor(self.dictOfBools[name1],
                                    self.dictOfBools[name2]))
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] < self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] >= self.dictOfReals[name3])
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
                name3 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str((0, 0))
                name3 += '_' + str(index_of_phi2)
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] == self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] != self.dictOfReals[name3])
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] > self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] <= self.dictOfReals[name3])
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] >= self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] < self.dictOfReals[name3])
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] <= self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] > self.dictOfReals[name3])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'constant_probability':
            constant = RealVal(hyperproperty.children[0].value) #.as_fraction().limit_denominator(10000)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            name = "prob"
            r_state = [(0, 0) for _ in range(self.no_of_stutter_quantifier)]
            for tup in r_state:
                name += "_" + str(tup)
            name += '_' + str(index_of_phi)
            self.addToVariableList(name)
            self.solver.add(self.dictOfReals[name] == constant)
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
                    self.solver.add(self.dictOfReals[name1] == (
                            self.dictOfReals[name2] + self.dictOfReals[name3]))
                    self.no_of_subformula += 2
                elif hyperproperty.data == 'subtract_probability':
                    self.solver.add(self.dictOfReals[name1] == (
                            self.dictOfReals[name2] - self.dictOfReals[name3]))
                    self.no_of_subformula += 2
                elif hyperproperty.data == 'multiply_probability':
                    self.solver.add(self.dictOfReals[name1] == (
                            self.dictOfReals[name2] * self.dictOfReals[name3]))
                    self.no_of_subformula += 2
                else:
                    print("Unexpected operator. Exiting")
                    return -1
            return relevant_quantifier

        else:
            self.encodeSemantics(hyperproperty.children[0])

    def addToVariableList(self, name):
        if name[0] == 'h' and not name.startswith('holdsToInt'):  # and name not in self.dictOfBools.keys():
            self.dictOfBools[name] = Bool(name)
        elif (name[0] in ['p', 'd', 'r', 'a', 't'] or name.startswith('holdsToInt')):  # and name not in self.dictOfReals.keys():
            self.dictOfReals[name] = Real(name)

    def generateComposedStatesWithStutter(self, list_of_relevant_quantifier):
        """
        Generates combination of states with stuttering based on relevant quantifiers
        :param list_of_relevant_quantifier: ranges from value 1- (no. of quantifiers)
        :return: list of composed states.
        """
        states_with_stuttering = list(
            itertools.product(self.model.getListOfStates(), list(range(self.stutterLength))))

        stored_list = []
        for quant in range(1, self.no_of_stutter_quantifier + 1):
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
        for quant in range(1, self.no_of_stutter_quantifier + 1):
            if quant in list_of_relevant_quantifier:
                stored_list.append(self.model.getListOfStates())
            else:
                stored_list.append([0])
        return list(itertools.product(*stored_list))

    def genSucc(self, r_state, ca, relevant_quantifier):
        """
        Generate successors of r_state under ca, with respect to relevant_quantifiers
        :param r_state: tuple of states with stuttering, of length no_of_stutter_quantifiers
        :param ca: chosen actions, length len(relevant_quantifier)
        :param relevant_quantifier: list of relevant stutter quantifiers
        :return: list with entries ["successor state", "probability of reaching that state"]
        """
        dicts = []
        for l in range(len(relevant_quantifier)):
            succ = self.model.dict_of_acts_tran[str(r_state[relevant_quantifier[l] - 1][0]) + " " + str(ca[l])]
            list_of_all_succ = []
            for s in succ:
                space = s.find(' ')
                succ_state = (int(s[0:space]), 0)
                list_of_all_succ.append((str(succ_state), s[space + 1:]))
            if r_state[relevant_quantifier[l]-1][1] < self.stutterLength - 1:
                list_of_all_succ.append((str((r_state[relevant_quantifier[l] - 1][0],
                                          r_state[relevant_quantifier[l] - 1][1] + 1)),
                                         str(1)))
            dicts.append(list_of_all_succ)
        return list(itertools.product(*dicts))

    def encodeNextSemantics(self, hyperproperty, prev_relevant_quantifier=[]):
        """
        encode Semantics of Next formulas
        :param hyperproperty: property of the form P(X phi1)
        :param prev_relevant_quantifier: previously relevant quantifiers
        :return: relevant_quantifier
        """
        print("\nNow encoding: " + str(hyperproperty))
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        relevant_quantifier = self.encodeSemantics(phi1, prev_relevant_quantifier)
        combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)

        for r_state in combined_state_list:
            print(".", end="")
            # encode relationship between holds and holdsToInt
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
                And(self.dictOfReals[holdsToInt1] == RealVal(1),
                    self.dictOfBools[holds1]),
                And(self.dictOfReals[holdsToInt1] == RealVal(0),
                    Not(self.dictOfBools[holds1])))
            self.solver.add(first_and)
            self.no_of_subformula += 3

            # create list of all possible actions for r_state
            dicts_act = []
            for l in range(len(relevant_quantifier)):
                dicts_act.append(self.model.dict_of_acts[r_state[relevant_quantifier[l] - 1][0]])
            combined_acts = list(itertools.product(*dicts_act))

            # encode probability calculation
            sum_of_probs_list = []
            for ca in combined_acts:
                # create list of successors of r_state with probabilities under currently considered stuttering and actions
                combined_succ = self.genSucc(r_state, ca, relevant_quantifier)

                # calculate probability based on probabilities that phi1 holds in the successor states
                for cs in combined_succ:
                    holdsToInt_succ = 'holdsToInt'
                    product_list = []

                    for l in range(1, self.no_of_stutter_quantifier + 1):
                        if l in relevant_quantifier:
                            l_index = relevant_quantifier.index(l)
                            succ_state = cs[l_index][0]
                            A = set(self.model.dict_of_acts[r_state[l - 1][0]])

                            holdsToInt_succ += '_' + succ_state

                            product_list.append(
                                self.dictOfReals['go_' + str(l) + '_' + str(r_state[l - 1]) + '_' + str(
                                    ca[l_index]) + '_' + cs[l_index][0]])
                            product_list.append(self.dictOfReals["a_" + str(A) + "_" + str(ca[l_index])])
                            product_list.append(self.dictOfReals[
                                                    'Tr_' + str(l) + '_' + str(r_state[l - 1]) + '_' + str(
                                                        ca[l_index]) + '_' + cs[l_index][0]])

                        else:
                            holdsToInt_succ += '_' + str((0, 0))

                    holdsToInt_succ += '_' + str(index_of_phi1)
                    self.addToVariableList(holdsToInt_succ)

                    product_list.append(self.dictOfReals[holdsToInt_succ])
                    sum_of_probs_list.append(Product(product_list))
                    self.no_of_subformula += 1

            probability_encoding = self.dictOfReals[prob_phi] == Sum(sum_of_probs_list)
            self.no_of_subformula += 1
            self.solver.add(probability_encoding)
            self.no_of_subformula += 1

        return relevant_quantifier

    def encodeUnboundedUntilSemantics(self, hyperproperty, relevant_quantifier=[]):
        """
        encode Semantics of Unbounded Until formulas
        :param hyperproperty: property of the form P(phi1 U phi2)
        :param prev_relevant_quantifier: previously relevant quantifiers
        :return: relevant_quantifier
        """
        print("\nNow encoding: " + str(hyperproperty))
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
            print(".", end="")
            # encode cases where we know probability is 0 or 1 and require probs variables to be in [0,1]
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

            first_implies = And(Implies(self.dictOfBools[holds2],
                                        (self.dictOfReals[prob_phi] == RealVal(1))),
                                Implies(And(Not(self.dictOfBools[holds1]),
                                            Not(self.dictOfBools[holds2])),
                                        (self.dictOfReals[prob_phi] == RealVal(0))))
            self.solver.add(first_implies)
            self.no_of_subformula += 4

            # create list of all possible actions for r_state
            dicts_act = []
            for l in range(len(relevant_quantifier)):
                dicts_act.append(self.model.dict_of_acts[r_state[relevant_quantifier[l] - 1][0]])
            combined_acts = list(itertools.product(*dicts_act))

            implies_precedent = And(self.dictOfBools[holds1], Not(self.dictOfBools[holds2]))

            # encode probability calculation
            sum_of_probs_list = []
            loop_condition = []

            for ca in combined_acts:
                # create list of successors of r_state with probabilities under currently considered stuttering and actions
                combined_succ = self.genSucc(r_state, ca, relevant_quantifier)

                # create equation system for probabilities and a loop condition to ensure correctness
                for cs in combined_succ:
                    prob_succ = 'prob'
                    holds_succ = 'holds'
                    d_current = 'd'
                    d_succ = 'd'

                    product_list = []
                    sched_prob_list = []

                    for l in range(1, self.no_of_stutter_quantifier + 1):
                        if l in relevant_quantifier:
                            l_index = relevant_quantifier.index(l)
                            succ_state = cs[l_index][0]
                            A = set(self.model.dict_of_acts[r_state[l - 1][0]])

                            prob_succ += '_' + succ_state
                            holds_succ += '_' + succ_state
                            d_succ += '_' + succ_state

                            product_list.append(self.dictOfReals['go_' + str(l) + '_' + str(r_state[l - 1]) + '_' + str(
                                ca[l_index]) + '_' + cs[l_index][0]])
                            product_list.append(self.dictOfReals["a_" + str(A) + "_" + str(ca[l_index])])
                            product_list.append(self.dictOfReals[
                                                    'Tr_' + str(l) + '_' + str(r_state[l - 1]) + '_' + str(
                                                        ca[l_index]) + '_' + cs[l_index][0]])

                            sched_prob_list.append(self.dictOfReals["a_" + str(A) + "_" + str(ca[l_index])])
                            sched_prob_list.append(self.dictOfReals[
                                                       'go_' + str(l) + '_' + str(r_state[l - 1]) + '_' + str(
                                                           ca[l_index]) + '_' + cs[l_index][0]])
                        else:
                            prob_succ += '_' + str((0, 0))
                            holds_succ += '_' + str((0, 0))
                            d_succ += '_' + str((0, 0))
                        d_current += '_' + str(r_state[l - 1])

                    prob_succ += '_' + str(index_of_phi)
                    self.addToVariableList(prob_succ)

                    product_list.append(self.dictOfReals[prob_succ])
                    sum_of_probs_list.append(Product(product_list))
                    self.no_of_subformula += 1

                    # loop condition
                    holds_succ += '_' + str(index_of_phi2)
                    self.addToVariableList(holds_succ)
                    d_current += '_' + str(index_of_phi2)
                    self.addToVariableList(d_current)
                    d_succ += '_' + str(index_of_phi2)
                    self.addToVariableList(d_succ)
                    loop_condition.append(And(Product(sched_prob_list) > RealVal(0),  #
                                              Or(self.dictOfBools[holds_succ],
                                                 self.dictOfReals[d_current] > self.dictOfReals[d_succ])
                                              ))
                    self.no_of_subformula += 3

            # implies_antecedent_and1 = self.dictOfReals[prob_phi] == sum_of_probs
            implies_antecedent_and1 = self.dictOfReals[prob_phi] == Sum(sum_of_probs_list)
            self.no_of_subformula += 1
            implies_antecedent_and2 = Implies(self.dictOfReals[prob_phi] > RealVal(0),
                                              Or(loop_condition))
            self.no_of_subformula += 2
            implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
            self.no_of_subformula += 1
            self.solver.add(Implies(implies_precedent, implies_antecedent))
            self.no_of_subformula += 1

        return relevant_quantifier

    def encodeFutureSemantics(self, hyperproperty, relevant_quantifier=[]):
        """
        encode Semantics of Future formulas
        :param hyperproperty: property of the form P(X phi1)
        :param prev_relevant_quantifier: previously relevant quantifiers
        :return: relevant_quantifier
        """
        print("\nNow encoding: " + str(hyperproperty))
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        rel_quant = self.encodeSemantics(phi1)
        relevant_quantifier = extendWithoutDuplicates(relevant_quantifier, rel_quant)
        combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)

        for r_state in combined_state_list:
            print(".", end="")
            # encode cases where we know probability is 1 and require probs variables to be in [0,1]
            holds1 = 'holds'
            str_r_state = ""
            for ind in r_state:
                str_r_state += "_" + str(ind)
            holds1 += str_r_state + "_" + str(index_of_phi1)
            self.addToVariableList(holds1)
            prob_phi = 'prob'
            prob_phi += str_r_state + '_' + str(index_of_phi)
            self.addToVariableList(prob_phi)

            first_implies = And(Implies(self.dictOfBools[holds1],
                                        (self.dictOfReals[prob_phi] == RealVal(1)))) # .as_fraction()
            self.solver.add(first_implies)
            self.no_of_subformula += 3

            # create list of all possible actions for r_state
            dicts_act = []
            for l in range(len(relevant_quantifier)):
                dicts_act.append(self.model.dict_of_acts[r_state[relevant_quantifier[l] - 1][0]])
            combined_acts = list(itertools.product(*dicts_act))

            implies_precedent = Not(self.dictOfBools[holds1])

            # sum_of_probs = RealVal(0).as_fraction() #
            sum_of_probs_list = []
            loop_condition = []

            for ca in combined_acts:
                # create list of successors of r_state with probabilities under currently considered stuttering and actions
                combined_succ = self.genSucc(r_state, ca, relevant_quantifier)

                # create equation system for probabilities and a loop condition to ensure correctness
                for cs in combined_succ:
                    prob_succ = 'prob'
                    holds_succ = 'holds'
                    d_current = 'd'
                    d_succ = 'd'

                    product_list = []
                    sched_prob_list = []

                    for l in range(1, self.no_of_stutter_quantifier + 1):
                        if l in relevant_quantifier:
                            l_index = relevant_quantifier.index(l)
                            succ_state = cs[l_index][0]
                            A = set(self.model.dict_of_acts[r_state[l - 1][0]])

                            prob_succ += '_' + succ_state
                            holds_succ += '_' + succ_state
                            d_succ += '_' + succ_state

                            product_list.append(self.dictOfReals['go_' + str(l) + '_' + str(r_state[l - 1]) + '_' + str(
                                                        ca[l_index]) + '_' + cs[l_index][0]])
                            product_list.append(self.dictOfReals["a_" + str(A) + "_" + str(ca[l_index])])
                            product_list.append(self.dictOfReals[
                                                    'Tr_' + str(l) + '_' + str(r_state[l - 1]) + '_' + str(
                                                        ca[l_index]) + '_' + cs[l_index][0]])

                            sched_prob_list.append(self.dictOfReals["a_" + str(A) + "_" + str(ca[l_index])])
                            sched_prob_list.append(self.dictOfReals[
                                                       'go_' + str(l) + '_' + str(r_state[l - 1]) + '_' + str(
                                                           ca[l_index]) + '_' + cs[l_index][0]])
                        else:
                            prob_succ += '_' + str((0, 0))
                            holds_succ += '_' + str((0, 0))
                            d_succ += '_' + str((0, 0))
                        d_current += '_' + str(r_state[l - 1])

                    prob_succ += '_' + str(index_of_phi)
                    self.addToVariableList(prob_succ)

                    product_list.append(self.dictOfReals[prob_succ])
                    sum_of_probs_list.append(Product(product_list))
                    self.no_of_subformula += 1

                    # loop condition
                    holds_succ += '_' + str(index_of_phi1)
                    self.addToVariableList(holds_succ)
                    d_current += '_' + str(index_of_phi1)
                    self.addToVariableList(d_current)
                    d_succ += '_' + str(index_of_phi1)
                    self.addToVariableList(d_succ)
                    loop_condition.append(And(Product(sched_prob_list) > RealVal(0),  #
                                              Or(self.dictOfBools[holds_succ],
                                                 self.dictOfReals[d_current] > self.dictOfReals[d_succ])
                                              ))
                    self.no_of_subformula += 3

            implies_antecedent_and1 = self.dictOfReals[prob_phi] == Sum(sum_of_probs_list)
            self.no_of_subformula += 1
            implies_antecedent_and2 = Implies(self.dictOfReals[prob_phi] > RealVal(0),
                                              Or(loop_condition))
            self.no_of_subformula += 2
            implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
            self.no_of_subformula += 1
            self.solver.add(Implies(implies_precedent, implies_antecedent))
            self.no_of_subformula += 1
        return relevant_quantifier

    def encodeGlobalSemantics(self, hyperproperty, relevant_quantifier=[]):
        print("\nNow encoding: " + str(hyperproperty))
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        rel_quant1 = self.encodeSemantics(phi1)
        relevant_quantifier = extendWithoutDuplicates(rel_quant1, relevant_quantifier)
        combined_state_list = self.generateComposedStatesWithStutter(relevant_quantifier)

        for r_state in combined_state_list:
            print(".", end="")
            # encode cases where we know probability is 0 and require probs variables to be in [0,1]
            holds1 = 'holds'
            str_r_state = ""
            for tup in r_state:
                str_r_state += "_" + str(tup)
            holds1 += str_r_state + "_" + str(index_of_phi1)
            self.addToVariableList(holds1)
            prob_phi = 'prob'
            prob_phi += str_r_state + '_' + str(index_of_phi)
            self.addToVariableList(prob_phi)

            first_implies = And(Implies((Not(self.dictOfBools[holds1])),
                                        (self.dictOfReals[prob_phi] == RealVal(0))))
            self.solver.add(first_implies)
            self.no_of_subformula += 1

            # create list of all possible actions for r_state
            dicts_act = []
            for l in range(len(relevant_quantifier)):
                dicts_act.append(self.model.dict_of_acts[r_state[relevant_quantifier[l] - 1][0]])
            combined_acts = list(itertools.product(*dicts_act))

            implies_precedent = self.dictOfBools[holds1]

            sum_of_probs_list = []
            loop_condition = []

            for ca in combined_acts:
                # create list of successors of r_state with probabilities under currently considered stuttering and actions
                combined_succ = self.genSucc(r_state, ca, relevant_quantifier)

                # create equation system for probabilities and a loop condition to ensure correctness
                for cs in combined_succ:
                    prob_succ = 'prob'
                    holds_succ = 'holds'
                    d_current = 'd'
                    d_succ = 'd'

                    product_list = []
                    sched_prob_list = []

                    for l in range(1, self.no_of_stutter_quantifier + 1):
                        if l in relevant_quantifier:
                            l_index = relevant_quantifier.index(l)
                            succ_state = cs[l_index][0]
                            A = set(self.model.dict_of_acts[r_state[l - 1][0]])

                            prob_succ += '_' + succ_state
                            holds_succ += '_' + succ_state
                            d_succ += '_' + succ_state

                            product_list.append(self.dictOfReals['go_' + str(l) + '_' + str(r_state[l - 1]) + '_' + str(
                                ca[l_index]) + '_' + cs[l_index][0]])
                            product_list.append(self.dictOfReals["a_" + str(A) + "_" + str(ca[l_index])])
                            product_list.append(self.dictOfReals[
                                                    'Tr_' + str(l) + '_' + str(r_state[l - 1]) + '_' + str(
                                                        ca[l_index]) + '_' + cs[l_index][0]])

                            sched_prob_list.append(self.dictOfReals["a_" + str(A) + "_" + str(ca[l_index])])
                            sched_prob_list.append(self.dictOfReals[
                                                       'go_' + str(l) + '_' + str(r_state[l - 1]) + '_' + str(
                                                           ca[l_index]) + '_' + cs[l_index][0]])
                        else:
                            prob_succ += '_' + str((0, 0))
                            holds_succ += '_' + str((0, 0))
                            d_succ += '_' + str((0, 0))
                        d_current += '_' + str(r_state[l - 1])

                    prob_succ += '_' + str(index_of_phi)
                    self.addToVariableList(prob_succ)

                    product_list.append(self.dictOfReals[prob_succ])
                    sum_of_probs_list.append(Product(product_list))
                    self.no_of_subformula += 1

                    # loop condition
                    holds_succ += '_' + str(index_of_phi1)
                    self.addToVariableList(holds_succ)
                    d_current += '_' + str(index_of_phi1)
                    self.addToVariableList(d_current)
                    d_succ += '_' + str(index_of_phi1)
                    self.addToVariableList(d_succ)
                    loop_condition.append(And(Product(sched_prob_list) > RealVal(0),
                                              Or(Not(self.dictOfBools[holds_succ]),
                                                 self.dictOfReals[d_current] > self.dictOfReals[d_succ])
                                              ))
                    self.no_of_subformula += 3

            implies_antecedent_and1 = self.dictOfReals[prob_phi] == Sum(sum_of_probs_list)
            self.no_of_subformula += 1
            implies_antecedent_and2 = Implies(self.dictOfReals[prob_phi] < RealVal(1),
                                              Or(loop_condition))
            self.no_of_subformula += 2
            implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
            self.no_of_subformula += 1
            self.solver.add(Implies(implies_precedent, implies_antecedent))
            self.no_of_subformula += 1

        return relevant_quantifier
