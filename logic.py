import read

# Ling Lin: llg8421
# Yue Shao: ysk9916
# Date: Oct 28, 2017
# Group work statement: All group members were present and contributing during all work
# on this project.

# A fact class that has fields of the following:
# statement-the statement of a fact, type of string
# supported_by-a list of facts and rules that support the fact
# asserted- whether the fact is in the kb or not
# facts_support-a list of facts that the fact support
# rules_support-a list of rules that the fact support
class Fact(object):
    def __init__(self, statement, supported_by = []):
        self.statement = statement
        self.supported_by = supported_by
        self.asserted = False
        self.facts_support = []
        self.rules_support = []

# A rule class that has fields of the following:
# statement-the statement of a fact, type of string
# supported_by-a list of facts and rules that support the rule
# asserted-whether the rule is in the kb or not
# facts_support-a list of facts that the rule support
# rules_support-a list of rules that the rule support
# lhs-the left hand side pattern of the rule, type of string
# rhs-the right hand side pattern of the rule, type of string
class Rule(object):
    def __init__(self, statement, supported_by = []):
        self.statement = statement
        self.supported_by = supported_by
        self.asserted = False
        self.facts_support = []
        self.rules_support = []
        self.lhs = statement[0]
        self.rhs = statement[1]

# A KB class that has fields of the following:
# add_fact-add the fact into the kb
# add_rule-add the rule into the kb
# kb_assert-assert a rule or fact
class kb(object):
    def __init__(self):
        self.facts = []
        self.rules = []

    def add_fact(self, fact):
        self.facts.append(fact)

    def add_rule(self, rule):
        self.rules.append(rule)

    def remove_fact(self, fact):
        self.facts.remove(fact)

    def remove_rule(self, rule):
        self.rules.remove(rule)

   

def KB_assert(kb, statement):
    if type(statement) == list:
        fact = Fact(statement)
        fact.asserted = True
        kb.add_fact(fact)
        infer_from_fact(kb, fact)
        return fact
    else:
        rule = Rule(statement)
        rule.asserted = True
        kb.add_rule(rule)
        infer_from_rule(kb, rule)
        return rule



# Used to match two statements to see if they can be interpreted as the same statement
# We use a dictionary to store the binding pairs. Then we check if s1 is a pattern or a fact, as well as s2. If s1 and s2
# are both patterns, we can not match them. Then we can which is the pattern, which is the fact. If the predicates of
# pattern and fact are not the same, we cannot match them either. fFor each variable in the pattern, we will match it with
# the corresponding value, and add them to the binding list.
def match(s1, s2):
    if len(s1) != len(s2):
        return False
    bindings = {}
    s1_flag = is_pattern(s1)
    s2_flag = is_pattern(s2)
    if s1_flag and s2_flag:
        return bindings
    elif s1_flag:
        pattern = s1
        fact = s2
    else:
        pattern = s2
        fact = s1
    if pattern[0] == fact[0]:
        for x in range(1, len(pattern)):
            if pattern[x][0] == '?':
                value = bindings.get(pattern[x], False)
                if ~value:
                    bindings[pattern[x]] = fact[x]
                elif value != fact[x]:
                    return False
            elif pattern[x] != fact[x]:
                return False
        return bindings
    else:
        return False

# Used to decide the statement is a pattern or a fact
def is_pattern(statement):
    for x in range(1, len(statement)):
        if statement[x][0] == '?':
            return True
    return False

# Used to test to see if the statement is in the Knowledge Base
def KB_ask(kb, statement):
    result = []
    find(kb, statement, result)
    return result

# Used to test to see if the statements are in the Knowledge Base and are consistent with regard to the bindings
def KB_ask_plus(kb, list_of_statements):
    result = []
    for statement in list_of_statements:
        find(kb, statement, result)
    return result

# Used to find if a statement is in the KB and return the bindings
# If the statement is a pattern, we search in the facts in the KB to find the matched facts. If the statement is a fact,
# we search in the rules in the KB to the matched patterns of rules.
def find(kb, statement, result):
    if is_pattern(statement):
        for fact in kb.facts:
            curr_s = fact.statement
            binding = match(statement, curr_s)
            if binding != False:
                result.append(binding)
    elif statement_in_kb(kb, statement):
        for rule in kb.rules:
            for pattern in rule.lhs:
                lbinding = match(pattern, statement)
                if lbinding != False:
                    result.append(lbinding)
            rbinding = match(rule.rhs, statement)
            if rbinding != False:
                result.append(rbinding)

# Used to retract a fact or rule in the KB.
# Given a fact or rule, first we check if it is in the KB, if it is in the KB, we check if it is a fact or rule, then we
# do a recursive delete. In this way we can delete the the facts and rules that are inferred by it recursively until all
# the facts and rules came from it are deleted.




def KB_retract(kb, fact_or_rule):
    to_retract = statement_in_kb(kb, fact_or_rule)
    if to_retract:
        if type(fact_or_rule) == list:
            kb.remove_fact(to_retract)
        else:
            kb.remove_rule(to_retract)
        remove(kb, to_retract)

# Used to deleted the facts and rules inferred by the target recursively
def remove(kb, fact_or_rule):
    for i in fact_or_rule.facts_support:
        kb.remove_fact(i)
        for parent in i.supported_by:
            parent.facts_support.remove(i)
        remove(kb, i)

    for i in fact_or_rule.rules_support:
        kb.remove_rule(i)
        for parent in i.supported_by:
            parent.rules_support.remove(i)
        remove(kb, i)

# Used to test to see if the statement is in the Knowledge Base. For each fact that is true, print out the tree of
# fact/rule justifications for it.
# First we check if the statement is in the KB, if it is in the KB, we traverse through its parents, which are the
# facts and rules in the supported_by list of that statement recursively.
def KB_why(kb, statement):
    found = statement_in_kb(kb, statement)
    if found != False:
        trace = []
        result = []
        traverse(kb, found, trace, result)
        print "=============Here are the tree nodes:============="
        for i in trace:
            if type(i) == str:
                print i
            else:
                print i.statement
        print "=======================END========================"
        return result
    else:
        return False

# Used to traverse the origins of the a statement.
# We use 'tarce' to store the traversal path of the origin tree and 'result' to store all the top level facts and rules
# that matched. When we traverse the origin tree of a statement, we just keep check the supported_by list of it to find
# all its parents, and then do this process recursively until we meet an origin statement. If we found a statement with
# an empty supported_by list, then it is an origin statement, we can add it to the 'result' list.
def traverse(kb, parent, trace, result):
    trace.append(parent)
    if parent.supported_by == []:
        result.append(parent)
        trace.append('null')
    else:
        for grand in parent.supported_by:
            traverse(kb, grand, trace, result)




# Given a pattern and a list of bindings, return a statement in which
# variables are instantiated with actual values
def instantiate(pattern, bindings):
    statement = [pattern[0]]
    constants = map(lambda x: bindings.get(x, x), pattern[1:])
    for i in constants:
        statement.append(i)
    return statement



# A helper function that checks whether a statement is in the kb
def statement_in_kb(kb, statement):
    if type(statement) == list:
        for f in kb.facts:
            if f.statement == statement:
                return f
        return False
    else:
        for r in kb.rules:
            if r.statement == statement:
                return r
        return False

# A helper function that checks whether a statement is in a list
def statement_in_list(kb, statement, list):
    for i in list:
        if i.statement == statement:
            return True
    return False


# Given a fact, infer a new fact or new rule from the fact
def infer_from_fact(kb, fact):
    for rule in kb.rules:
        bindings = match(rule.lhs[0], fact.statement)
        if bindings != False:
            infer(kb, rule, fact, bindings)

# Given a rule, infer a new fact or new rule from the rule
def infer_from_rule(kb, rule):
    for fact in kb.facts:
        bindings = match(rule.lhs[0], fact.statement)
        if bindings != False:
            infer(kb, rule, fact, bindings)

# Given a rule, a fact and a list of bindings,
# find out what we could infer from them
def infer(kb, rule, fact, bindings):

    # If the length of the right hand side of the rule is one,
    # meaning that we may infer a new fact.
    if len(rule.lhs) == 1:

        # Create a statement that can be inferred from
        # the right hand side of the rule and the bindings.
        infered_statement = instantiate(rule.rhs, bindings)

        # Check if the fact is already in the kb, if not, return false, if so, return the fact
        same_fact_in_kb = statement_in_kb(kb, infered_statement)

        # If the inferred fact is not already in the kb,
        # then assert the inferred fact into the kb,
        # in the mean time, update the supported_by list
        # as well as facts_support list and rules_support list.
        if same_fact_in_kb == False:
            infered_fact = KB_assert(kb, infered_statement)
            infered_fact.supported_by = [fact, rule]
            if statement_in_list(kb, infered_fact.statement, fact.facts_support) == False:
                fact.facts_support.append(infered_fact)
            if statement_in_list(kb, infered_fact.statement, rule.facts_support) == False:
                rule.facts_support.append(infered_fact)
            infer_from_fact(kb, infered_fact)

        # If the inferred fact is already in the kb, only update the supported_by list
        # as well as facts_support list and rules_support list if needed.
        else:
            if statement_in_list(kb, fact.statement, same_fact_in_kb.supported_by) == False:
                if same_fact_in_kb.supported_by == []:
                    same_fact_in_kb.supported_by = [fact]
                else:
                    same_fact_in_kb.supported_by.append(fact)
            fact.facts_support.append(same_fact_in_kb)
            if statement_in_list(kb, rule.statement, same_fact_in_kb.supported_by) == False:
                if same_fact_in_kb.supported_by == []:
                    same_fact_in_kb.supported_by = [rule]
                else:
                    same_fact_in_kb.supported_by.append(rule)
            rule.facts_support.append(same_fact_in_kb)

    # If the length of the right hand side of the rule is more than one,
    # meaning that it may infer a new rule, and same thing as infer a new fact
    else:
        infered_lhs = instantiate(rule.lhs[1], bindings)
        infered_rhs = instantiate(rule.rhs, bindings)
        infered_statement = ([infered_lhs], infered_rhs)
        same_rule_in_kb = statement_in_kb(kb, infered_statement)
        if same_rule_in_kb == False:
            infered_rule = KB_assert(kb, infered_statement)
            infered_rule.supported_by = [fact, rule]

            if statement_in_list(kb, infered_rule.statement, fact.rules_support) == False:

                fact.rules_support.append(infered_rule)
            if statement_in_list(kb, infered_rule.statement, rule.rules_support) == False:
                rule.rules_support.append(infered_rule)
            infer_from_rule(kb, infered_rule)
        else:
            if statement_in_list(kb, fact.statement, same_rule_in_kb.supported_by) == False:
                if same_rule_in_kb.supported_by == []:
                    same_rule_in_kb.supported_by = [fact]
                else:
                    same_rule_in_kb.supported_by.append(fact)


            if statement_in_list(kb, same_rule_in_kb.statement, fact.rules_support) == False:

                fact.rules_support.append(same_rule_in_kb)

            if statement_in_list(kb, rule.statement, same_rule_in_kb.supported_by) == False:
                if same_rule_in_kb.supported_by == []:
                    same_rule_in_kb.supported_by = [rule]
                else:
                    same_rule_in_kb.supported_by.append(rule)

            if statement_in_list(kb, same_rule_in_kb.statement, rule.rules_support) == False:
                rule.rules_support.append(same_rule_in_kb)







# Test cases

# kb.kb_assert(([['inst', '?x', '?y'], ['isa', '?y', '?z']], ['color', '?x', '?z']))
#
# kb.kb_assert(['inst', 'cube1', 'cube'])
#
# kb.kb_assert(['isa', 'cube', 'red'])
#
# print "======================facts================================"
#
# for f in kb.facts:
#     print "----------------------------------------------"
#     print f.statement
#
#     print "supported_by:"
#     for s in f.supported_by:
#         print s.statement
#
#     print "facts_support:"
#     for s in f.facts_support:
#         print s.statement
#
#     print "rules_support:"
#     for s in f.rules_support:
#         print s.statement
#
#
# print "=====================rules================================="
#
#
#
# for f in kb.rules:
#     print "----------------------------------------------"
#     print f.statement
#
#     print "supported_by:"
#     for s in f.supported_by:
#         print s.statement
#
#     print "facts_support:"
#     for s in f.facts_support:
#         print s.statement
#
#     print "rules_support:"
#     for s in f.rules_support:
#         print s.statement
#
#
