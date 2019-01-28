import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        #has to be a fact or a rule not asserted
        if isinstance(fact_or_rule, Fact):
            n = self._get_fact(fact_or_rule)
        else:
            n = self._get_rule(fact_or_rule)
        if isinstance(n, Rule) and n.asserted: return
        if isinstance(n,Fact):
            if n.asserted or len(n.supported_by) == 0:
                for s in n.supported_by:
                    s[0].supports_facts.remove(n)
                    s[1].supports_facts.remove(n)
            if len(n.supported_by) != 0: return
           
        if isinstance(n,Rule):
            if n.asserted: return
            for s in n.supported_by:
                s[0].supports_rules.remove(n)
                s[1].supports_rules.remove(n)
        if isinstance(n, Fact): self.facts.remove(n)
        if isinstance(n, Rule): self.rules.remove(n)

        for f in n.supports_facts:
            for i in f.supported_by:
                if (i[0] == n):
                    f.supported_by.remove(i)
                    self._pass_on_fact(f)
            if (len(f.supported_by) == 0):
                self.kb_retract(f)
        for f in n.supports_rules:
            for i in f.supported_by:
                if (i[0] == n):
                    f.supported_by.remove(i)
                    self._pass_on_rule(f)
            if (len(f.supported_by) == 0):
                self.kb_retract(f)

    def _pass_on_fact(self, fact):
        for i in range(len(self.facts)):
            if (self.facts[i] == fact):
                self.facts[i] = fact

    def _pass_on_rule(self, rule):
        for i in range(len(self.rules)):
            if (self.rules[i] == rule):
                self.rules[i] = rule


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv("Attempting to infer from {!r} and {!r} => {!r}", 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        bindings = match(fact.statement, rule.lhs[0])
        if bindings:
            lhs = []
            for l in rule.lhs: lhs.append(instantiate(l, bindings))
            if (fact.statement == lhs[0] and len(lhs) > 1): lhs.remove(lhs[0])
            rhs = instantiate(rule.rhs, bindings)

            newrule = Rule([lhs, rhs], [[fact, rule]])
            fact.supports_rules.append(newrule)
            rule.supports_rules.append(newrule)
            kb.kb_assert(newrule)
            '''add new fact. The rule is if there is a fact that correspond to
               every single statement on the left hand side you can make the right hand
               side a new fact
            '''
            if self.newFact(lhs, kb):
                newFact = Fact(rhs, [[fact, rule]])
                fact.supports_facts.append(newFact)
                rule.supports_facts.append(newFact)
                kb.kb_assert(newFact)
        
            printv("Support from {!r} and {!r} => {!r}, {!r}", 1, verbose,
                   [fact.statement, fact.supports_facts, rule.rhs, rule.supports_facts])

    
    def newFact(self, lhs, kb):
        '''See if the kb has facts that correspond to EVERY single statement in lhr of rule
            
            Args:
            lhs: newly generated left hand side: list of statements
            kb: knowledge base
            
            Returns:
              a boolean tells whether or nor we can generate a new fact
        '''
        for l in lhs:
             b = False
             for f in kb.facts:
                 if (f.statement == l): b = True
             if not(b): return b
        return True





