class Prop(object):
    """
    Recall the Prop class from HW7 to represent propositions of the form:
    A, not A, A and B, A or B, A imp B
    where A and B can be any variables (can also be ALPHA, BETA, or any string).
    """

    def __init__(self,conn,p1,p2):

        assert conn in ["at","and","not","or","imp"]

        if conn in ["and","or","imp"]:
            assert isinstance(p1,Prop)
            assert isinstance(p2,Prop)
        elif conn == "not":
            assert isinstance(p1,Prop)
            assert p2 is None
        else: # atomic expression
            assert isinstance(p1,str)
            assert p2 is None

        self.conn = conn
        self.p1 = p1
        self.p2 = p2

    def __str__(self):
        """
        returns a string that represents the proposition where:
        - '&' represents and
        - 'v' represents or
        - '->' represents implies
        - '~' represents not
        """
        if self.conn == "not":
            return "~(" + str(self.p1) + ")"
        elif self.conn == "at":
            return str(self.p1) 
        elif self.conn == "imp":
            return "(" + str(self.p1) + ") -> (" + str(self.p2) + ")"
        elif self.conn == "or":
            return "(" + str(self.p1) + ") v (" +  str(self.p2) + ")"
        elif self.conn == "and":
            return "(" + str(self.p1) + ") & (" +  str(self.p2) + ")"



    def __eq__(self, other):
        """
        returns True iff self and other are the same propositions
        (i.e. same structure and same variables, just like any binary tree equality)
        """
        return self.conn == other.conn and self.p1 == other.p1 and self.p2 == other.p2
    
    def getvars(self):
        ans = []
        if self.conn == "at":
            ans += [self.p1]
        elif self.conn == "not":
            ans +=  self.p1.getvars()
        else:
            ans += self.p1.getvars() + self.p2.getvars()
        ans = elim_reps(ans)
        return ans
    


class Sequent(object):
    """
    Recall the Sequent class from LAB10, which represents a sequent
    using with two lists of propositions, 
    the antecedent (gamma) and the consequent (delta).
    """

    def __init__(self, antecedent, consequent):
        # make sure that every element in the list antecedent is of type Prop
        for p in antecedent:
            assert isinstance(p,Prop)
        # make sure that every element in the list consequent is of type Prop
        for p in consequent:
            assert isinstance(p,Prop)

        self.ant = antecedent
        self.con = consequent

    def __str__(self):
        """
        returns a string that represents a sequent.
        We use '|--' to represent the turnstile.

        It should print all the propositions in self.ant (separated by a comma)
        using Prop __str__ method, then a turnstile and then all the
        propositions in self.con (separated by a comma).
        """
        left = ''
        right = ''
        for i in range(len(self.ant)):
                left += Prop.__str__(self.ant[i])  + ", "
      
        for i in range(len(self.con)):
                right += Prop.__str__(self.con[i]) + ", "
        return left[:-2] + '|-- ' + right[:-2]

    def is_atomic(self):
        """
        returns True iff all propositions in self.ant and self.con are atomic
        """
        found = True
        if self.ant is not None:
            for p in self.ant:
                if p.conn != 'at':
                    found = False
        if self.con is not None:
            for prop in self.con:
                if prop.conn !=  'at':
                    found= False
        return found
        

    def is_id(self):
        """
        returns True iff there is at least one proposition
        that is both in self.ant and self.con (using Prop __eq__ method)
        """
        found = False
        for p in self.ant:
            for prop in self.con:
                if p == prop:
                    found = True
        return found


class ProofTree(object):
    """
    A proof tree is a special binary tree where every node
    has a sequent and a rule associated with it.

    Also, like binary trees, every node has two subtrees, left and right, 
    that are either proof trees themselves or None.
    """

    def __init__(self, seq):
        # the root value is a sequent, i.e. |-- AvB 
        self.root = seq

        # initially, the left and right subtrees are None
        self.left_subtree = None
        self.right_subtree = None

        # initially, the rule is empty. As we "grow" the tree,
        # we fill in the rules that led from one sequent to another
        self.rule = ""

    def str_parse_tree(self,depth):
        s = depth  * ' '
        if self.right_subtree is None and self.left_subtree is None:
            return depth * ' ' + str(self.root)+ '\n'
        
        else:
            s = depth * ' ' + str(self.root) + '\n' + depth*' ' +self.rule 
            s += '\n' + self.left_subtree.str_parse_tree(depth+6)
            if self.right_subtree is not None:
                s += '\n' + self.right_subtree.str_parse_tree(depth+6) 
            return s
        

    def __str__(self):
        """
        This method should return a string that represents the proof tree.
        You are free to choose whatever representation you like, as long
        as one can read the proof *clearly* from it.
        This should give you something like:

        |--  ((~(A)) v (~(B))) -> (~((A) & (B)))
        imp right
                  (~(A)) v (~(B))  |--  ~((A) & (B))
                  or left
                            ~(A)  |--  ~((A) & (B))
                            not left
                                      |--  A,~((A) & (B))
                                      not right
                                                (A) & (B)  |--  A
                                                and left
                                                          A,B  |--  A
                                                          
                            ~(B)  |--  ~((A) & (B))
                            not left
                                      |--  B,~((A) & (B))
                                      not right
                                                (A) & (B)  |--  B
                                                and left
                                                          A,B  |--  B

        """
        return self.str_parse_tree(0)
        
            
    def get_leaves(self):
        """
        returns a list of all sequents in the leaves of the tree
        """
        l = []
        r = []
        if self.left_subtree is None and self.right_subtree is None:
            return [self.root]
        else:
            if self.left_subtree is not None:
                l = self.left_subtree.get_leaves()
            if self.right_subtree is not None:
                r = self.right_subtree.get_leaves()
            return l + r

    def build_proof(self):
        """
        This method populates the tree with a proof. i.e.
        it applies sequent rules until all the leaves are atomic sequents.

        Note that nothing should be returned. Instead, self should be mutated.
        """
        if not self.root.is_atomic():
            l = apply_rule(self.root)
            self.left_subtree = ProofTree(l[0])
            if l[1] != None:
                self.right_subtree = ProofTree(l[1])               
            if self.left_subtree is not None:
                self.rule = l[2]
                left_tree= ProofTree(self.left_subtree.build_proof())
            if self.right_subtree is not None:
                self.rule = l[2]
                right_tree = ProofTree(self.right_subtree.build_proof())
        
   

def apply_rule(seq):
    """
    apply a rule to the left most non atomic proposition in seq
    and return a list of 3 elements:
        - the obtained first sequent
        - the obtained second sequent or None if the rule
          has only one resulting sequent (i.e. does not cause a split)
        - a string representing the rule that was applied

    Important note: the function does NOT mutate seq.
    """
    for idx,prop in enumerate(seq.ant):

        if prop.conn == "not":
            # create a copy of seq (we don't want to mutate it)
            new_seq = Sequent(seq.ant[:],seq.con[:])
            # pop the proposition from the list
            not_a = new_seq.ant.pop(idx)
            # make sure we popped the correct one
            assert not_a.conn == "not"
            # apply the rule
            new_seq.con = [ not_a.p1 ] + new_seq.con
            # return a list of 3 values with seq2 being None
            # (since there is not split in this rule)
            return [new_seq , None, "not left"]

        elif prop.conn == "or":
            # create two copies of seq
            new_seq1 = Sequent(seq.ant[:], seq.con[:])
            new_seq2 = Sequent(seq.ant[:], seq.con[:])
            # pop the proposition from the list
            b_or_c = new_seq1.ant.pop(idx)
            # make sure we popped the correct one
            assert b_or_c.conn == "or"
            assert b_or_c == new_seq2.ant.pop(idx)
            # apply the rule
            new_seq1.ant.append(b_or_c.p1)
            new_seq2.ant.append(b_or_c.p2)
            # return the obtained sequents and the rule name
            # here we have two sequents since "or left"
            # has two sequents at the top
            return [new_seq1 , new_seq2, "or left"]

        elif prop.conn == "and":
            #create one copy of seq
            new_seq = Sequent(seq.ant[:], seq.con[:])
            # pop the proposition from the list
            b_and_c = new_seq.ant.pop(idx)
            # make sure we popped the correct one
            assert b_and_c.conn == "and"
            # apply the rule
            new_seq.ant.append(b_and_c.p1)
            new_seq.ant.append(b_and_c.p2)
            # return a list of 3 values with seq2 being None
            return [new_seq, None, 'and left']

            
        elif prop.conn == "imp":
            # create two copies of seq
            new_seq1 = Sequent(seq.ant[:], seq.con[:])
            new_seq2 = Sequent(seq.ant[:], seq.con[:])
            # pop the proposition from the list
            b_imp_c = new_seq1.ant.pop(idx)
            # make sure we popped the correct one
            assert b_imp_c.conn == "imp"
            assert b_imp_c == new_seq2.ant.pop(idx)
            # apply the rule
            new_seq1.ant.append(b_imp_c.p2)
            new_seq2.con.append(b_imp_c.p1)
            # return the obtained sequents and the rule name
            return [new_seq1 , new_seq2, "implies left"]

    for idx,prop in enumerate(seq.con):
        if prop.conn == "not":
            new_seq = Sequent(seq.ant[:],seq.con[:])
            # pop the proposition from the list
            not_a = new_seq.con.pop(idx)
            # make sure we popped the correct one
            assert not_a.conn == "not"
            # apply the rule
            new_seq.ant = [ not_a.p1 ] + new_seq.ant
            # return a list of 3 values with seq2 being None
            return [new_seq , None, "not right"]
        elif prop.conn == "or":
            # create one copy of seq
            new_seq = Sequent(seq.ant[:], seq.con[:])
            # pop the proposition from the list
            b_or_c = new_seq.con.pop(idx)
            # make sure we popped the correct one
            assert b_or_c.conn == "or"            
            # apply the rule
            new_seq.con.append(b_or_c.p1)
            new_seq.con.append(b_or_c.p2)
            # return the obtained sequent and the rule name
            return [new_seq , None, "or right"]

        elif prop.conn == 'and':
            new_seq1 = Sequent(seq.ant[:], seq.con[:])
            new_seq2 = Sequent(seq.ant[:], seq.con[:])
            b_and_c = new_seq1.con.pop(idx)
            assert b_and_c.conn == "and"
            assert b_and_c == new_seq2.con.pop(idx)
            new_seq1.con.append(b_and_c.p1)
            new_seq2.con.append(b_and_c.p2)
            return [new_seq1 , new_seq2, "and right"]

        elif prop.conn == 'imp':
            new_seq = Sequent(seq.ant[:], seq.con[:])
            b_imp_c = new_seq.con.pop(idx)
            assert b_imp_c.conn == "imp"
            new_seq.ant.append(b_imp_c.p1)
            new_seq.con.append(b_imp_c.p2)
            return [new_seq , None, "implies right"]

            
            

def prove_or_disprove(prop):
    """
    this function either prints a proof tree (if prop is a tautology)
    or prints a counter example (if prop is not a tautology)

    Hint: you should construct a new proof tree with the sequent |-- prop 
    and then call build_proof() and check the leaves:
        - if all the leave are identities, then you have a proof and
          you can simply call ProofTree __str__ method to print it
        - otherwise, if you have an atomic sequent that is not identity,
          you can use it to print a counter example. Think about how!
          To print the counter example, you can print a list of tuples of the form
          ('A',T), ('B', F), etc
          or you can use a different form (as long as it states clearly the
          assignment of variables to truth values).
    """
    #create sequent
    sequent = Sequent([],[prop])
    #create proof tree
    tree = ProofTree(sequent)
    tree.build_proof()
    #check leaves
    found = True
    seq_leaves = tree.get_leaves()
    for s in seq_leaves:
        if s.is_id() == False:
            assign(prop, s)
            found = False
            break
    if found == True:
        print tree
    
def elim_reps(lst):
    """
    for getvars, part of class prop
    lst:any list
    return: lst with all repetitions removed
    """
    ans = []
    for x in lst:
        if x not in ans:
            ans.append(x)
    return ans

def assign(prop,leaf):
    new_lst = []
    list_left = []
    list_right = []
    list_prop = prop.getvars()    
    for a in leaf.ant:
        if str(a) in list_prop:
            list_prop.remove(str(a))
        if (str(a),True) not in list_left:
            list_left.append((str(a), True))      
    for c in leaf.con:
        if str(c) in list_prop:
            list_prop.remove(str(c))
        if (str(c),False) not in list_right:
            list_right.append((str(c), False))         
    for item in list_prop:
        new_lst.append((str(item), False))
    new_lst += (list_left)
    new_lst += (list_right)
    print new_lst

# SOME EXAMPLES AND TESTS



# a_anb_b_imp_a = A and B --> A"
a = Prop("at",'A',None)
b = Prop("at",'B',None)
a_anb_b = Prop("and",a,b)

print "expecting (something like): (A) & (B) ; result: ", a_anb_b
print "expecting: False ; result: ", a_anb_b == a

a_anb_b_imp_a = Prop("imp",a_anb_b,a)
seq = Sequent([],[a_anb_b_imp_a])
print "expecting (something like): |--  ((A) & (B)) -> (A) ; result: ", seq
print "expecting: False ; result: ", seq.is_id()
print "expecting: False ; result: ", seq.is_atomic()

tree = ProofTree(seq)
tree.build_proof()
print "expecting a proof"
print tree

print "printing leaves. all of them should be atomic and id"
seq_leaves = tree.get_leaves()
for s in seq_leaves:
    print "leaf:", s, " ; is_id: ", s.is_id(), " ; is_atomic: ", s.is_atomic()

print "expecting a proof to |--  ((A) & (B)) -> (A)"
prove_or_disprove(a_anb_b_imp_a)

# prop = (((A --> B) --> A) --> B
a_imp_b = Prop("imp", a, b)
a_imp_b_imp_a = Prop("imp", a_imp_b, a)
prop = Prop("imp", a_imp_b_imp_a, b)

print "expecting (something like): (A) -> (B) ; result: ", a_imp_b
print "expecting (something like): ((A) -> (B)) -> (A) ; result: ", a_imp_b_imp_a
print "expecting (something like): (((A) -> (B)) -> (A)) -> (B) ; result: ", prop

seq = Sequent([],[prop])
print "expecting: |--  (((A) -> (B)) -> (A)) -> (B) ; result: ", seq
print "expecting: False ; result: ", seq.is_id()
print "expecting: False ; result: ", seq.is_atomic()

tree = ProofTree(seq)
tree.build_proof()
print "expecting a failed proof"
print tree

print "printing leaves. all of them should be atomic and at least one should not be id"
seq_leaves = tree.get_leaves()
for s in seq_leaves:
    print "leaf:", s, " ; is_id: ", s.is_id(), " ; is_atomic: ", s.is_atomic()

print "expecting a counter example for: ", prop
print "for example: [('A', True), ('B', False)]"
prove_or_disprove(prop)
print "\n"

# not (A and B) --> (not A or not B)
not_a_anb_b = Prop("not",a_anb_b,None)
not_a = Prop("not",a,None)
not_b = Prop("not",b,None)
not_a_or_not_b = Prop("or", not_a, not_b)
prop = Prop("imp", not_a_anb_b, not_a_or_not_b)
print "expecting a proof for: |--", prop
prove_or_disprove(prop)

# (not A or not B) -->  not (A and B)
prop = Prop("imp", not_a_or_not_b, not_a_anb_b)
print "expecting a proof for: |--", prop
prove_or_disprove(prop)

# (((A --> B) --> A) --> A
a_imp_b = Prop("imp", a, b)
a_imp_b_imp_a = Prop("imp", a_imp_b, a)
prop = Prop("imp",a_imp_b_imp_a,a)
print "expecting a proof for: |--", prop
prove_or_disprove(prop)

# not (A and B) --> (not A and not B)
not_a_and_not_b = Prop("and", not_a, not_b)
prop = Prop("imp", not_a_anb_b, not_a_and_not_b)
print "expecting a counter example for: ", prop
prove_or_disprove(prop)
print "\n"


# (A --> B) --> ((A --> not B) --> (not A))
a_imp_not_b = Prop("imp", a, not_b)
prop = Prop("imp", a_imp_b, Prop("imp", a_imp_not_b, not_a))
print "expecting a proof for: |--", prop
prove_or_disprove(prop)

# ((A or B) and ( A --> C and B --> C)) --> C
c = Prop("at","C",None)
a_or_b = Prop("or", a, b)
a_imp_c = Prop("imp", a, c)
b_imp_c = Prop("imp", b, c)
prop = Prop("imp", Prop("and", a_or_b, Prop("and", a_imp_c, b_imp_c)), c)
print "expecting a proof for: |--", prop
prove_or_disprove(prop)

#assign helper function test

d = Prop('at','A',None)
e = Prop('at','B',None)
f = Prop('at','C',None)

leaf = Sequent([d],[f,f])

assign(prop,leaf)




