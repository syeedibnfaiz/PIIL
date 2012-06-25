/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package ca.uwo.csd.piil;

import java.util.ArrayList;
import java.util.HashMap;

/**
 * Solver class implements methods to produce interpretation scheme/pattern for
 * a set of propositional partial information ionic logic formulas using analytic
 * tableau method. Work flows as follows:<pre>
 *                         solve([a->b, -b])
 *                                |
 *                            [-b, a->b]
 *                                |
 *                         expand([-b, a->b])
 *                                |
 *                           applyRule(-b)
 *                                |
 *                       expand([NPT b, a->b])
 *                                |
 *                         applyRule(a -> b)
 *                          /            \
 *           expand([NPT b, NPT a])   expand([NPT b, T b])
 *                 |                             |
 *     checkClosure([NPT b, NPT a])   checkClosure([NPT b, T b])
 *                 |                             |
 *       <{NPT b, NPT a}, {}, {}>               null
 * </pre>
 * @author Syeed Ibn Faiz
 */
public class Solver {

    /**
     * Produces interpretation schemes for a set of PPIIL formulas. It rearranges
     * the content of the list so that the non-branching formulas precede the
     * branching ones. Then the new list is expanded using <code>expand</code>.
     * @param list a list of PPIIL formulas
     * @return a set of interpretation schemes
     */
    public ArrayList<Interpretation> solve(ArrayList<Formula> list) {
        ArrayList<Formula> branchingList = new ArrayList<Formula>();
        ArrayList<Formula> nonBranchingList = new ArrayList<Formula>();
        for (Formula f : list) {
            if (isBranching(f)) {
                branchingList.add(f);
            } else {
                nonBranchingList.add(f);
            }
        }
        nonBranchingList.addAll(branchingList);
        list = nonBranchingList;

        return expand(list);
    }

    /**
     * Expands a branch of a tableau. <code>list</code> represents a branch in the
     * tableau. <code>expand</code> finds the first formula in the branch for which
     * expansion rule can be applied and which is not already extended(used before).
     * If this formula is branching then <code>expand</code> calls itself twice for
     * each branch and merges the result of each of them. Otherwise if this formula
     * does not create branch then <code>expand</code> calls itself recursively for
     * the updated branch and return the result.
     * @param list a list of formulas in a branch of tableau
     * @return set of interpretation schemes
     */
    private ArrayList<Interpretation> expand(ArrayList<Formula> list) {
        boolean expanded = false;

        /*System.out.print("Expanding: [ ");
        for(Formula f: list) {
            if (!f.isExpanded()) System.out.print(f + " ");
        }
        System.out.println("]");*/

        for (int i = 0; i < list.size(); i++) {
            if (!list.get(i).isExpanded()) {                        //applyRule marks formulas once rule is applied for them
                ArrayList<ArrayList<Formula>> ll = null;
                ll = applyRule(list.get(i));
                if (ll == null || ll.isEmpty()) {                   //e.g. applyRule(PT bot(a)) returns an empty list
                    continue;
                } else if (ll.size() == 1) {                        //e.g. applyRule(NPT a -> b)
                    expanded = true;
                    ArrayList<Formula> oldList = new ArrayList<Formula>(list);
                    list = addAll(list, ll.get(0));
                    ArrayList<Interpretation> result = expand(list);

                    list = oldList = null;
                    return result;
                } else if (ll.size() == 2) {                        //e.g. applyRule(T a -> b)
                    expanded = true;                    

                    ArrayList<Formula> oldList = list;              //keeping exact set of references
                    boolean exp[] = new boolean[oldList.size()];
                    //saving expansion info to restore for right branch
                    for(int j = 0; j < oldList.size(); j++) {
                        exp[j] = oldList.get(j).isExpanded();
                    }
                    
                    list = new ArrayList<Formula>(oldList);
                    list = addAll(list, ll.get(0));
                    ArrayList<Interpretation> result1 = expand(list);

                    //restoring expansion status for formulas
                    for(int j = 0; j < oldList.size(); j++) {
                        oldList.get(j).setExpanded(exp[j]);
                    }
                    list = new ArrayList<Formula>(oldList);
                    list = addAll(list, ll.get(1));
                    ArrayList<Interpretation> result2 = expand(list);

                    list = oldList = null;                                     //releasing references
                    if (result1 == null) {
                        return result2;
                    } else if (result2 == null) {
                        return result1;
                    } else {
                        result1.addAll(result2);
                        return result1;
                    }
                }
            }
        }
        if (expanded == false) {
            return checkClosure(list);
        }
        return null;

    }

    /**
     * Checks whether a branch is closed or not.
     * @param list a set of formulas representing a branch of tableau
     * @return null if the branch is closed, otherwise an interpretation
     * satisfying the branch.
     */
    private ArrayList<Interpretation> checkClosure(ArrayList<Formula> list) {
                
        if (list == null || list.isEmpty()) {            
            return null;
        }

        /*System.out.printf("{");
        boolean first = true;
        for (int i = 0; i < list.size(); i++) {
            if (list.get(i).getType() != Formula.ATOMIC || list.get(i).getQuantifier() != Formula.NONE) {
                continue;
            }
            if (!first) {
                System.out.printf(",");
            } else first = false;
            System.out.printf("%s ", list.get(i));
        }
        System.out.printf("}\n");*/

        ArrayList<Formula> atomList = new ArrayList<Formula>();
        for (int i = 0; i < list.size(); i++) {
            //pick all atomic formulas unless they are canonical justification formulas
            //generic justification formulas are not included
            if (list.get(i).getType() == Formula.ATOMIC && (list.get(i).getQuantifier() == Formula.NONE /*|| list.get(i).getQuantifier() == Formula.GENJUST*/)) {
                if (list.get(i).getVar().equalsIgnoreCase("False") && (list.get(i).getSign() != Formula.NOT_POT_TRUE && list.get(i).getSign() != Formula.NOT_TRUE)) {
                    return null;
                    
                } else if (list.get(i).getVar().equalsIgnoreCase("True") && (list.get(i).getSign() != Formula.TRUE && list.get(i).getSign() != Formula.POT_TRUE)) {
                    return null;

                } else if (!list.get(i).getVar().equalsIgnoreCase("True") && !list.get(i).getVar().equalsIgnoreCase("False")) {
                    atomList.add(list.get(i));
                }
            } else if (list.get(i).getCntv() == '@' && list.get(i).getSign() == Formula.NOT_POT_TRUE) {
                //NPT bot(a) -> closed
                return null;
            }
        }

        
        int T = Formula.TRUE;               //0000
        int NT = Formula.NOT_TRUE;          //0010
        int PT = Formula.POT_TRUE;          //0100
        int NPT = Formula.NOT_POT_TRUE;     //0110
        int H = Formula.HARD;
        int S = Formula.SOFT;
        int J = Formula.JUST;
        int G = Formula.GENJUST;

        //closure rules not involving the generic operator
        for (int i = 0; i < atomList.size(); i++) {
            Formula a1 = atomList.get(i);
            for (int j = 0; j < atomList.size(); j++) {
                if (i == j) continue;
                
                Formula a2 = atomList.get(j);
                if (a1.getVar().equalsIgnoreCase(a2.getVar())) {

                    int sign1 = a1.getSign();
                    int sign2 = a2.getSign();

                    if (prefixMatches(a1.getJPrefix(), a2.getJPrefix())) {              //8.3.4 (i) generalized closure rule
                        //if ((a1.getQuantifier() != G || a2.getKnowledgeType() != S) && (a1.getKnowledgeType() != S || a2.getQuantifier() != G)) {
                            if ((sign1^sign2) == 2 || (sign1 == T && sign2 == NPT) || (sign2 == T && sign1 == NPT) ) return null;
                        //}

                    } else if (prefixEndsWith(a2.getJPrefix(), a1.getJPrefix())) {
                        if (a1.getKnowledgeType() != S && a2.getKnowledgeType() != S) { //8.3.4 (ii) jKnowledge extends hKnowledge
                            if ((sign1^sign2) == 2 || (sign1 == T && sign2 == NPT) || (sign2 == T && sign1 == NPT)) return null;

                        } else if (a2.getKnowledgeType() == S) {                        //8.3.4 (iii) sKnowledge extends hKnowledge
                            if ((sign1^sign2) == 2 || (sign1 == T && sign2 == NPT) || (sign2 == T && sign1 == NPT)) return null;
                        }
                    }
                }
            }
        }        
        //System.out.println("Not closed without generic.");
        //closure rule involving generic operator
        for (int i = 0; i < list.size(); i++) {
            Formula f1 = list.get(i);
            int sign1 = f1.getSign();
            if (f1.getType() == Formula.ATOMIC && f1.getVar().equalsIgnoreCase("False") && (f1.getSign() != Formula.NOT_POT_TRUE && f1.getSign() != Formula.NOT_TRUE)) {
                return null;
            } else if (f1.getType() == Formula.ATOMIC && f1.getVar().equalsIgnoreCase("True") && (f1.getSign() != Formula.TRUE && f1.getSign() != Formula.POT_TRUE)) {
                return null;
            }
            for (int j = 0; j < list.size(); j++) {
                if (i == j) continue;
                Formula f2 = list.get(j);
                int sign2 = f2.getSign();

                if ((f1.getKnowledgeType()==H && f1.getRank() == 0) && f2.getQuantifier()==G && equals(f1, f2)) {  //Theorem 8.3.7
                    if ((sign1^sign2) == 2 || (sign1 == T && sign2 == NPT) || (sign2 == T && sign1 == NPT)) {
                        //System.out.println("Theorem 8.3.7");
                        return null;
                    }
                } else if ((f1.getKnowledgeType()==H && f1.getRank() == 0) && f2.getQuantifier()==G && (f2.getCntv()=='-' && equals(f1, f2.getChild(0)))) {  //Theorem 8.3.7 equivalent variant
                    if ((sign1==NPT && (sign2==NPT || sign2==NT)) || (sign1==T && (sign2==T || sign2==PT))) {
                        //System.out.println("Here");
                        return null;
                    }
                    
                } else if (f1.getQuantifier() == G && f2.getQuantifier() == G) {    //Theorem 8.3.8
                    if ( equals(f1, f2) && ((sign1^sign2) == 2 || (sign1 == T && sign2 == NPT) || (sign2 == T && sign1 == NPT))) {
                        //System.out.println("Theorem 8.3.8_1, " + f1 + ": " + f1.getQuantifier() + ", "+ f2 + ": " + f2.getQuantifier());
                        return null;
                    }
                    else if (f1.getCntv()=='&' && (equals(f1.getChild(0), f2) || equals(f1.getChild(1), f2)) && sign1==T && sign2==NPT) {
                        //System.out.println("Theorem 8.3.8_2");
                        return null;
                    } else if (f1.getCntv()=='>' && equals(f1.getChild(1), f2)) {
                        if ((sign1==NPT&&sign2==PT)||(sign1==NT&&sign2==T)||(sign1==NPT&&sign2==T)) {
                            //System.out.println("Theorem 8.3.8_3");
                            return null;
                        }
                    }
                }
            }
        }

        //System.out.println("not closed..");
        //include all generic justification formula
        for (int i = 0; i < list.size(); i++) {
            if (list.get(i).getQuantifier() == Formula.GENJUST) {
                //atomList.add(list.get(i));
                if (list.get(i).getType() != Formula.ATOMIC || (!list.get(i).getVar().equalsIgnoreCase("True") && !list.get(i).getVar().equalsIgnoreCase("False"))) {
                    atomList.add(list.get(i));
                }
            }
        }
        ArrayList<Interpretation> result = new ArrayList<Interpretation>();
        result.add(new Interpretation(atomList));
        return result;
    }

    /**
     * Tests whether two given formulas are identical.
     * @param f1
     * @param f2
     * @return
     */
    private boolean equals(Formula f1, Formula f2) {
        if (f1.getRank() != f2.getRank()) return false;
        else if (f1.getCntv() != f2.getCntv()) return false;
        else if (f1.getType() == Formula.COMP_BINARY){
            return (equals(f1.getChild(0), f2.getChild(0)) && equals(f1.getChild(1), f2.getChild(1)));
        }else if (f1.getType() == Formula.COMP_UNARY){
            return (equals(f1.getChild(0), f2.getChild(0)));
        } else {
            //System.out.println(f1.getVar() + " " + f2.getVar());
            return (f1.getVar().equals(f2.getVar()));
        }
    }
    /**
     * Tests whether two justification prefixes match or not.
     * @param j1
     * @param j2
     * @return true if <code>j1</code> matches with <code>j2</code>
     */
    private boolean prefixMatches(ArrayList<Justification> j1, ArrayList<Justification> j2) {
        if (j1 == null && j2 == null) return true;
        if (j1 == null || j2 == null) return false;
        if (j1.size() != j2.size()) return false;

        for (int i = 0; i < j1.size(); i++) {
            if (!j1.get(i).equals(j2.get(i))) return false;
        }
        return true;
    }

    /**
     * Tests whether one justification prefix ends with another one.
     * @param jp
     * @param e
     * @return true if <code>e</code> is a suffix of <code>jp</code>
     */
    private boolean prefixEndsWith(ArrayList<Justification> jp, ArrayList<Justification> e) {
        if (e == null) return true;
        if (jp == null || e.size() > jp.size()) return false;

        for (int i = 0; i < e.size(); i++) {
            if (!e.get(i).equals(jp.get(i))) return false;
        }
        return true;
    }
    /**
     * Merges two lists of formulas so that the non-branching formulas appear before
     * the branching ones.
     * @param l1
     * @param l2
     * @return
     */
    private ArrayList<Formula> addAll(ArrayList<Formula> l1, ArrayList<Formula> l2) {
        ArrayList<Formula> nonBranching = new ArrayList<Formula>();
        for (int i = 0; i < l2.size(); i++) {
            if (isBranching(l2.get(i))) {
                l1.add(l2.get(i));
            } else {
                nonBranching.add(l2.get(i));
            }
        }
        if (nonBranching.isEmpty()) {
            return l1;
        } else {
            nonBranching.addAll(l1);
            return nonBranching;
        }
    }

    /**
     * Apply tableau expansion rule for a formula. For example,
     * applyRule(T a -> b) returns [[NPT a], [T b]]
     * applyRule(NPT a -> b) returns [[T a, NPT b]]
     * @param f a formula
     * @return a list of list of formulas
     */
    private ArrayList<ArrayList<Formula>> applyRule(Formula f) {
        ArrayList<ArrayList<Formula>> ll = new ArrayList<ArrayList<Formula>>();
        f.setExpanded(true);
        
        //System.out.println("Applying rule for " + f);
        
        /* Shortcuts */
        final int T = Formula.TRUE;
        final int NT = Formula.NOT_TRUE;
        final int PT = Formula.POT_TRUE;
        final int NPT = Formula.NOT_POT_TRUE;
        final int U = Formula.UNIV;
        final int E = Formula.EXIST;
        final int S = Formula.SOFT;
        final int J = Formula.JUST;
        final int KT = f.getKnowledgeType();
        
        ArrayList<Justification> JP = f.getJPrefix();
        
        if (f.getQuantifier() != Formula.NONE) {
            ArrayList<Formula> l = new ArrayList<Formula>();
            Formula g = new Formula(f.getSign(), KT, f, Formula.NONE, f.getJPrefix());
            if (f.getQuantifier() == E) {
                g.addJustification(new Justification(f.getRank(), false));
            } else {
                g.addJustification(new Justification(f.getRank(), true));
            }
            l.add(g);
            ll.add(l);

        } else if (f.getType() == Formula.ATOMIC) {
            return null;
        } else if (f.getCntv() == '-') {
            ArrayList<Formula> l = new ArrayList<Formula>();
            Formula g = f.getChild(0);
            switch (f.getSign()) {
                case T:
                    l.add(new Formula(NPT, KT, g, JP));
                    break;
                case NT:
                    l.add(new Formula(PT, KT, g, JP));
                    break;
                case PT:
                    l.add(new Formula(NT, KT, g, JP));
                    break;
                case NPT:
                    l.add(new Formula(T, KT, g, JP));
                    break;
            }
            ll.add(l);
        } else if (f.getCntv() == '~') {
            ArrayList<Formula> l = new ArrayList<Formula>();
            Formula g = f.getChild(0);
            switch (f.getSign()) {
                case T:
                    l.add(new Formula(NT, KT, g, JP));
                    break;
                case NT:
                    l.add(new Formula(T, KT, g, JP));
                    break;
                case PT:
                    l.add(new Formula(NT, KT, g, JP));
                    break;
                case NPT:
                    l.add(new Formula(T, KT, g, JP));
                    break;
            }
            ll.add(l);
        } else if (f.getCntv() == '#') {    //~'
            ArrayList<Formula> l = new ArrayList<Formula>();
            Formula g = f.getChild(0);
            switch (f.getSign()) {
                case T:
                    l.add(new Formula(NPT, KT, g, JP));
                    break;
                case NT:
                    l.add(new Formula(PT, KT, g, JP));
                    break;
                case PT:
                    l.add(new Formula(NPT, KT, g, JP));
                    break;
                case NPT:
                    l.add(new Formula(PT, KT, g, JP));
                    break;
            }
            ll.add(l);
        } else if (f.getCntv() == '@') {    //bot
            ArrayList<Formula> l1 = new ArrayList<Formula>();
            ArrayList<Formula> l2 = new ArrayList<Formula>();
            Formula g = f.getChild(0);
            switch (f.getSign()) {
                case T:
                    l1.add(new Formula(PT, KT, g, JP));
                    l1.add(new Formula(NT, KT, g, JP));
                    break;
                case NT:
                    l1.add(new Formula(T, KT, g, JP));
                    l2.add(new Formula(NPT, KT, g, JP));
                    break;
                case PT:
                case NPT:
                    return null;
            }
            ll.add(l1);
            if (!l2.isEmpty()) {
                ll.add(l2);
            }
        } else if (f.getCntv() == '&') {
            ArrayList<Formula> l1 = new ArrayList<Formula>();
            ArrayList<Formula> l2 = new ArrayList<Formula>();
            Formula g1 = f.getChild(0);
            Formula g2 = f.getChild(1);
            switch (f.getSign()) {
                case T:
                    l1.add(new Formula(T, KT, g1, JP));
                    l1.add(new Formula(T, KT, g2, JP));
                    break;
                case NT:
                    l1.add(new Formula(NT, KT, g1, JP));
                    l2.add(new Formula(NT, KT, g2, JP));
                    break;
                case PT:
                    l1.add(new Formula(PT, KT, g1, JP));
                    l1.add(new Formula(PT, KT, g2, JP));
                    break;
                case NPT:
                    l1.add(new Formula(NPT, KT, g1, JP));
                    l2.add(new Formula(NPT, KT, g2, JP));
                    break;
            }
            if (!l1.isEmpty()) {
                ll.add(l1);
            }
            if (!l2.isEmpty()) {
                ll.add(l2);
            }

        } else if (f.getCntv() == '|') {
            ArrayList<Formula> l1 = new ArrayList<Formula>();
            ArrayList<Formula> l2 = new ArrayList<Formula>();
            Formula g1 = f.getChild(0);
            Formula g2 = f.getChild(1);
            switch (f.getSign()) {
                case T:
                    l1.add(new Formula(T, KT, g1, JP));
                    l2.add(new Formula(T, KT, g2, JP));
                    break;
                case NT:
                    l1.add(new Formula(NT, KT, g1, JP));
                    l1.add(new Formula(NT, KT, g2, JP));
                    break;
                case PT:
                    l1.add(new Formula(PT, KT, g1, JP));
                    l2.add(new Formula(PT, KT, g2, JP));
                    break;
                case NPT:
                    l1.add(new Formula(NPT, KT, g1, JP));
                    l1.add(new Formula(NPT, KT, g2, JP));
                    break;
            }
            if (!l1.isEmpty()) {
                ll.add(l1);
            }
            if (!l2.isEmpty()) {
                ll.add(l2);
            }

        } else if (f.getCntv() == '>') {
            ArrayList<Formula> l1 = new ArrayList<Formula>();
            ArrayList<Formula> l2 = new ArrayList<Formula>();
            Formula g1 = f.getChild(0);
            Formula g2 = f.getChild(1);
            switch (f.getSign()) {
                case T:
                    l1.add(new Formula(NPT, KT, g1, JP));
                    l2.add(new Formula(T, KT, g2, JP));
                    break;
                case NT:
                    l1.add(new Formula(PT, KT, g1, JP));
                    l1.add(new Formula(NT, KT, g2, JP));
                    break;
                case PT:
                    l1.add(new Formula(NT, KT, g1, JP));
                    l2.add(new Formula(PT, KT, g2, JP));
                    break;
                case NPT:
                    l1.add(new Formula(T, KT, g1, JP));
                    l1.add(new Formula(NPT, KT, g2, JP));
                    break;
            }
            if (!l1.isEmpty()) {
                ll.add(l1);
            }
            if (!l2.isEmpty()) {
                ll.add(l2);
            }

        } else if (f.getCntv() == '!') {
            ArrayList<Formula> l1 = new ArrayList<Formula>();
            ArrayList<Formula> l2 = new ArrayList<Formula>();
            Formula g1 = f.getChild(0);
            Formula g2 = f.getChild(1);
            switch (f.getSign()) {
                case T:
                    l1.add(new Formula(T, KT, g1, JP));
                    l1.add(new Formula(T, KT, g2, JP));
                    break;
                case NT:
                    l1.add(new Formula(NT, KT, g1, JP));
                    l2.add(new Formula(NT, KT, g2, JP));
                    break;
                case PT:
                    l1.add(new Formula(PT, KT, g1, JP));
                    l2.add(new Formula(PT, KT, g2, JP));
                    break;
                case NPT:
                    l1.add(new Formula(NPT, KT, g1, JP));
                    l1.add(new Formula(NPT, KT, g2, JP));
                    break;
            }
            if (!l1.isEmpty()) {
                ll.add(l1);
            }
            if (!l2.isEmpty()) {
                ll.add(l2);
            }

        } else if (f.getCntv() == '*') {
            ArrayList<Formula> l1 = new ArrayList<Formula>();
            ArrayList<Formula> l2 = new ArrayList<Formula>();
            Formula g1 = f.getChild(0);
            Formula g2 = f.getChild(1);
            if (g2.getType() == Formula.ATOMIC && g2.getVar().equalsIgnoreCase("false")) {
                //nogood formula *(a, False)
                switch (f.getSign()) {
                    case T:
                        l1.add(new Formula(NPT, Formula.JUST, g1, JP));
                        break;
                    case NT:
                        l1.add(new Formula(PT, Formula.JUST, g1, JP));
                        break;
                    case PT:
                        l1.add(new Formula(NT, Formula.JUST, g1, JP));
                        break;
                    case NPT:
                        l1.add(new Formula(T, Formula.JUST, g1, JP));
                        break;
                }
                if (!l1.isEmpty()) {
                    for (Formula h : l1) {
                        h.setQuantifier(Formula.GENJUST);
                        h.setExpanded(true);
                    }
                    ll.add(l1);
                }
            } else {
                switch (f.getSign()) {
                    case T:
                        l1.add(new Formula(T, Formula.JUST, g1, JP));
                        l1.add(new Formula(T, S, g2, JP));
                        l2.add(new Formula(NPT, Formula.JUST, g1, JP));
                        break;
                    case NT:
                        l1.add(new Formula(PT, Formula.JUST, g1, JP));
                        l2.add(new Formula(PT, Formula.JUST, g1, JP));
                        l1.add(new Formula(NT, Formula.JUST, g1, JP));
                        l1.add(new Formula(T, S, g2, JP));
                        l2.add(new Formula(NT, S, g2, JP));
                        break;
                    case PT:
                        l1.add(new Formula(NT, Formula.JUST, g1, JP));
                        l1.add(new Formula(NPT, S, g2, JP));
                        l2.add(new Formula(PT, S, g2, JP));
                        break;
                    case NPT:
                        l1.add(new Formula(T, Formula.JUST, g1, JP));
                        l1.add(new Formula(NPT, S, g2, JP));
                        break;
                }
                if (!l1.isEmpty()) {
                    for (Formula h : l1) {
                        if (h.getKnowledgeType() == Formula.JUST) {
                            //System.out.println("preprocessed : " + h);
                            h.setQuantifier(Formula.GENJUST);
                            h.setExpanded(true);
                        }
                    }
                    ll.add(l1);
                }
                if (!l2.isEmpty()) {
                    for (Formula h : l2) {
                        if (h.getKnowledgeType() == Formula.JUST) {
                            h.setQuantifier(Formula.GENJUST);
                            h.setExpanded(true);
                        }
                    }
                    ll.add(l2);
                }
            }

        } else if (f.getCntv() == '0') {    // Diamondsuit <>
            int args[] = {
                NPT, U,         PT, E,      NPT, E,     PT, U,  //nogood
                PT, U,  T,      NPT, U,                         //True
                PT, E,  NPT, E, T, NT,                          //Not True
                NPT, E, NPT, PT,                                //Potentially True
                PT, U, NPT                                      //Not Potentially True
            };
            return applyCondIonRules1(f, args);

        } else if (f.getCntv() == '1') {    // HeartSuit (^)
            int args[] = {
                NT, U,      T, E,       NT, E,       T, E,  //nogood
                T, U,       T,          NT, U,              //True
                T, E,       NT, E,      T,    NT,           //Not True
                NT, E,      NPT,        PT,                 //Potentially True
                T, U,       NPT                             //Not Potentially True
            };
            return applyCondIonRules1(f, args);

        } else if (f.getCntv() == '2') {    // Circle O
            int args[] = {
                T , U,      T, E,       NT, E,       T, E,  //nogood
                T, U,       T,          NPT, U,              //True
                PT, E,      NT, E,      T,    NT,           //Not True
                NT, E,      NPT,        PT,                 //Potentially True
                T, U,       NPT                             //Not Potentially True
            };
            return applyCondIonRules1(f, args);

        } else if (f.getCntv() == '5') {    // Blackfly (Bullet) o
            int args[] = {
                NPT , U,    PT, E,      NT, U,       T, E,  //nogood
                T, E,       T,          NPT, U,              //True
                PT, E,      NT, U,      T,    NT,           //Not True
                NT, U,      NPT,        PT,                 //Potentially True
                T, E,       NPT                             //Not Potentially True
            };
            return applyCondIonRules1(f, args);

        } else if (f.getCntv() == '8') {    // Butterfly (Bullet-twin) |><|
            int args[] = {
                NPT , E,    PT, U,      NT, E,       T, U,  //nogood
                T, U,       T,          NPT, E,              //True
                PT, U,      NT, E,      T,    NT,           //Not True
                NT, E,      NPT,        PT,                 //Potentially True
                T, U,       NPT                             //Not Potentially True
            };
            return applyCondIonRules1(f, args);
            
        } else if (f.getCntv() == '3') {    //Spadesuit
            int args[] = {
                NPT , U,    PT, E,      NPT, U,       PT, E,  //nogood
                NPT, E,     T,          NPT, U,               //True
                PT, E,      NT,                               //Not True
                NPT, U,     NPT,        PT,                   //Potentially True
                PT, E,      NPT                               //Not Potentially True
            };
            return applyCondIonRules2(f, args);
        } else if (f.getCntv() == '4') {    //Clubsuit
            int args[] = {
                NT , U,    T, E,       NT, U,       T, E,    //nogood
                T, E,      T,          NT, U,                //True
                T, E,      NT,                               //Not True
                NT, U,     NPT,        PT,                   //Potentially True
                T, E,      NPT                               //Not Potentially True
            };
            return applyCondIonRules2(f, args);

        } else if (f.getCntv() == '6') {    //Spadesuit-twin
            int args[] = {
                NPT , E,    PT, U,       NPT, E,       PT, U,  //nogood
                PT, U,      T,           NPT, E,               //True
                PT, U,      NT,                                //Not True
                NPT, E,     NPT,         PT,                   //Potentially True
                PT, U,      NPT                                //Not Potentially True
            };
            return applyCondIonRules2(f, args);
            
        } else if (f.getCntv() == '7') {    //Clubsuit-twin
            int args[] = {
                NT , E,    T, U,       NT, E,       T, U,  //nogood
                T, U,      T,           NT, E,               //True
                T, U,      NT,                                //Not True
                NT, E,     NPT,         PT,                   //Potentially True
                T, U,      NPT                                //Not Potentially True
            };
            return applyCondIonRules2(f, args);
        }

        //System.out.println("Returning " + ll);
        return ll;
    }

    /**
     * Applies rules for conditional ion 0,1,2,5,8. Their structure differ from
     * from the rest in the rule for NT formulas. Parameters are used as follows:
     * <pre>     
     * T *0(f, false)   NT*0(f, false)    PT*0(f, false)   NPT*0(f, false)
     * |                |                 |                |
     * a0 f a1          a2 f a3           a4 f a5          a6 f a7
     * <br>
     *                   T *0(f1, f2)
     *     -------------------------------------------
     *    a8  f1 a9                         a11 f1 a12
     *    a10 f2
     *                  NT *0(f1, f2)
     *                  |
     *                  a13 f1 a14
     *    ---------------------------------------------
     *   a15 f1 a16                              a18 f2
     *   a17 f2
     *                  PT *0(f1, f2)
     *   ----------------------------------------------
     *   a19 f1 a20                              a22 f2
     *   a21 f2
     *                  NPT *0(f1, f2)
     *                  |
     *                  a23 f1 24
     *                  a25 f2
     * </pre>
     * @param f
     * @param args an array of length 26, containing all the parameters.
     * @return
     */
    private ArrayList<ArrayList<Formula>> applyCondIonRules1(Formula f, int args[]) {
        ArrayList<ArrayList<Formula>> ll = new ArrayList<ArrayList<Formula>>();
        ArrayList<Formula> l1 = new ArrayList<Formula>();
        ArrayList<Formula> l2 = new ArrayList<Formula>();
        Formula g1 = f.getChild(0);
        Formula g2 = f.getChild(1);
        if (g2.getType() == Formula.ATOMIC && g2.getVar().equalsIgnoreCase("false")) {
            //nogood formula *(a, False)
            switch (f.getSign()) {
                case Formula.TRUE:
                    l1.add(new Formula(args[0], Formula.JUST, g1, args[1], f.getJPrefix()));
                    break;
                case Formula.NOT_TRUE:
                    l1.add(new Formula(args[2], Formula.JUST, g1, args[3], f.getJPrefix()));
                    break;
                case Formula.POT_TRUE:
                    l1.add(new Formula(args[4], Formula.JUST, g1, args[5], f.getJPrefix()));
                    break;
                case Formula.NOT_POT_TRUE:
                    l1.add(new Formula(args[6], Formula.JUST, g1, args[7], f.getJPrefix()));
                    break;
            }
            if (!l1.isEmpty()) {
                ll.add(l1);
            }
        } else {
            switch (f.getSign()) {
                case Formula.TRUE:
                    l1.add(new Formula(args[8], Formula.JUST, g1, args[9], f.getJPrefix()));
                    l1.add(new Formula(args[10], Formula.SOFT, g2, f.getJPrefix()));
                    l2.add(new Formula(args[11], Formula.JUST, g1, args[12], f.getJPrefix()));
                    break;
                case Formula.NOT_TRUE:
                    l1.add(new Formula(args[13], Formula.JUST, g1, args[14], f.getJPrefix()));
                    l2.add(new Formula(args[13], Formula.JUST, g1, args[14], f.getJPrefix()));
                    l1.add(new Formula(args[15], Formula.JUST, g1, args[16], f.getJPrefix()));
                    l1.add(new Formula(args[17], Formula.SOFT, g2, f.getJPrefix()));
                    l2.add(new Formula(args[18], Formula.SOFT, g2, f.getJPrefix()));
                    break;
                case Formula.POT_TRUE:
                    l1.add(new Formula(args[19], Formula.JUST, g1, args[20], f.getJPrefix()));
                    l1.add(new Formula(args[21], Formula.SOFT, g2, f.getJPrefix()));
                    l2.add(new Formula(args[22], Formula.SOFT, g2, f.getJPrefix()));
                    break;
                case Formula.NOT_POT_TRUE:
                    l1.add(new Formula(args[23], Formula.JUST, g1, args[24], f.getJPrefix()));
                    l1.add(new Formula(args[25], Formula.SOFT, g2, f.getJPrefix()));
                    break;
            }
            if (!l1.isEmpty()) {
                ll.add(l1);
            }
            if (!l2.isEmpty()) {
                ll.add(l2);
            }
        }
        return ll;
    }

    /**
     * Applies rules for conditional ion 3,4,6,7. Parameters are used as follows:
     * <pre>
     * T *0(f, false)   NT*0(f, false)    PT*0(f, false)   NPT*0(f, false)
     * |                |                 |                |
     * a0 f a1          a2 f a3           a4 f a5          a6 f a7
     * <br>
     *                   T *0(f1, f2)
     *     -------------------------------------------
     *    a8  f1 a9                         a11 f1 a12
     *    a10 f2
     *                  NT *0(f1, f2)
     *                  |
     *                  a13 f1 a14
     *                  a15 f2
     * <br>
     *                  PT *0(f1, f2)
     *   ----------------------------------------------
     *   a16 f1 a17                              a19 f2
     *   a18 f2
     *                  NPT *0(f1, f2)
     *                  |
     *                  a20 f1 21
     *                  a22 f2
     * </pre>
     * @param f
     * @param args an array of length 23, containing all the parameters.
     * @return
     */
    private ArrayList<ArrayList<Formula>> applyCondIonRules2(Formula f, int args[]) {
        ArrayList<ArrayList<Formula>> ll = new ArrayList<ArrayList<Formula>>();
        ArrayList<Formula> l1 = new ArrayList<Formula>();
        ArrayList<Formula> l2 = new ArrayList<Formula>();
        Formula g1 = f.getChild(0);
        Formula g2 = f.getChild(1);
        if (g2.getType() == Formula.ATOMIC && g2.getVar().equalsIgnoreCase("false")) {
            //nogood formula *(a, False)
            switch (f.getSign()) {
                case Formula.TRUE:
                    l1.add(new Formula(args[0], Formula.JUST, g1, args[1], f.getJPrefix()));
                    break;
                case Formula.NOT_TRUE:
                    l1.add(new Formula(args[2], Formula.JUST, g1, args[3], f.getJPrefix()));
                    break;
                case Formula.POT_TRUE:
                    l1.add(new Formula(args[4], Formula.JUST, g1, args[5], f.getJPrefix()));
                    break;
                case Formula.NOT_POT_TRUE:
                    l1.add(new Formula(args[6], Formula.JUST, g1, args[7], f.getJPrefix()));
                    break;
            }
            if (!l1.isEmpty()) {
                ll.add(l1);
            }
        } else {
            switch (f.getSign()) {
                case Formula.TRUE:
                    l1.add(new Formula(args[8], Formula.JUST, g1, args[9], f.getJPrefix()));
                    l1.add(new Formula(args[10], Formula.SOFT, g2, f.getJPrefix()));
                    l2.add(new Formula(args[11], Formula.JUST, g1, args[12], f.getJPrefix()));
                    break;
                case Formula.NOT_TRUE:
                    l1.add(new Formula(args[13], Formula.JUST, g1, args[14], f.getJPrefix()));
                    l1.add(new Formula(args[15], Formula.SOFT, g2, f.getJPrefix()));
                    break;
                case Formula.POT_TRUE:
                    l1.add(new Formula(args[16], Formula.JUST, g1, args[17], f.getJPrefix()));
                    l1.add(new Formula(args[18], Formula.SOFT, g2, f.getJPrefix()));
                    l2.add(new Formula(args[19], Formula.SOFT, g2, f.getJPrefix()));
                    break;
                case Formula.NOT_POT_TRUE:
                    l1.add(new Formula(args[20], Formula.JUST, g1, args[21], f.getJPrefix()));
                    l1.add(new Formula(args[22], Formula.SOFT, g2, f.getJPrefix()));
                    break;
            }
            if (!l1.isEmpty()) {
                ll.add(l1);
            }
            if (!l2.isEmpty()) {
                ll.add(l2);
            }
        }
        return ll;
    }
    
    /**
     * Tests whether a formula would cause branching or not.
     * @param f
     * @return true is <code>f</code> is branching.
     */
    private boolean isBranching(Formula f) {
        if (f.getCntv() == '|') {
            if (f.getSign() == Formula.TRUE || f.getCntv() == Formula.POT_TRUE) {
                return true;
            } else {
                return false;
            }
        } else if (f.getCntv() == '&') {
            if (f.getSign() == Formula.NOT_TRUE || f.getCntv() == Formula.NOT_POT_TRUE) {
                return true;
            } else {
                return false;
            }
        } else if (f.getCntv() == '@') {
            if (f.getSign() == Formula.NOT_TRUE) {
                return true;
            } else {
                return false;
            }
        } else if (f.getCntv() == '>') {
            if (f.getSign() == Formula.TRUE || f.getCntv() == Formula.POT_TRUE) {
                return true;
            } else {
                return false;
            }
        } else if (f.getCntv() == '!') {
            if (f.getSign() == Formula.NOT_TRUE || f.getCntv() == Formula.POT_TRUE) {
                return true;
            } else {
                return false;
            }
        } else if (Character.isDigit(f.getCntv())) {
            if (f.getSign() == Formula.NOT_POT_TRUE) {
                return false;
            } else if ((f.getSign() == Formula.NOT_TRUE) && (f.getCntv() == '3' || f.getCntv() == '4' || f.getCntv() == '6' || f.getCntv() == '7')) {
                return false;
            } else {
                return true;
            }
        } else {
            return false;
        }
    }
}
