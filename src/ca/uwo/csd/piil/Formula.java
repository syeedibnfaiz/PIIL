/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package ca.uwo.csd.piil;

import java.util.ArrayList;

/**
 * The <code>Formula</code> represents a partial information ionic formula.
 * @author Syeed Ibn Faiz
 */
public class Formula {

    /* Constant values for turnstiles */
    public static final int UNKNOWN = 127;
    public static final int TRUE = 0;
    public static final int NOT_TRUE = 2;
    public static final int POT_TRUE = 4;
    public static final int NOT_POT_TRUE = 6;

    /* Formula Types */
    public static final int ATOMIC = 666;
    public static final int COMP_UNARY = 667;
    public static final int COMP_BINARY = 668;

    /* Type of knowledge */
    public static final int HARD = 777;
    public static final int SOFT = 778;
    public static final int JUST = 779;

    /* Quantifier */
    public static final int UNIV = 888;
    public static final int EXIST = 999;
    public static final int NONE = 1111;
    public static final int GENJUST = 2222; //marker for generic justification

    private int sign;                       //turnstile
    private int type;                       //atomic/compound
    private int knowledge;                  //hard/soft/justification
    private int rank;
    private char cntv;                      //connective
    private boolean expanded;               //marked if used
    private String propVar;                 //stores propositional variable
    private ArrayList<Formula> childList;   //list of chindren    
    ArrayList<Justification> justPrefix;    //justification prefix
    int qn;                                 //quantifier

    /**
     * Constructs a <code>Formula</code> containing only a propositional variable.
     * @param s name of a propositional variable.
     */
    public Formula(String s) {
        this.sign = UNKNOWN;
        this.cntv = 0;
        this.type = ATOMIC;
        this.knowledge = UNKNOWN;
        this.propVar = s;
        this.childList = null;
        expanded = false;
        rank = 0;

        justPrefix = null;
        qn = NONE;
    }

    /**
     * Constructs an exact copy of a formula. Allocates new memory for everything.
     * @param old
     */
    public Formula(Formula old) {
        this.sign = old.sign;
        this.cntv = old.cntv;
        this.type = old.type;
        this.knowledge = old.knowledge;
        this.propVar = old.propVar;        
        this.rank = old.rank;
        this.qn = old.qn;
        expanded = old.expanded;
        
        this.childList = null;
        if (old.childList != null) {
            this.childList = new ArrayList<Formula>();
            for (Formula f : old.childList) {
                this.childList.add(new Formula(f));
            }
        }
        this.justPrefix = null;
        if (old.justPrefix != null) {
            this.justPrefix = new ArrayList<Justification>();
            for (Justification j : old.justPrefix) {
                this.justPrefix.add(j);
            }
        }
        
        
    }
    /**
     * Constructs a <code>Formula</code> with a unary connective applied to a given <code>Formula</code>.
     * @param cntv a unary connective
     * @param f a <code>Formula</code>
     */
    public Formula(char cntv, Formula f) {
        this.sign = UNKNOWN;
        this.cntv = cntv;
        this.type = COMP_UNARY;
        this.knowledge = UNKNOWN;
        this.propVar = null;
        this.childList = new ArrayList<Formula>();
        this.childList.add(f);
        expanded = false;
        rank = f.getRank();

        justPrefix = null;
        qn = NONE;
    }

    /**
     * Constructs a <code>Formula</code> with a binary connective applied to two given <code>Formula</code>s.
     * @param cntv a binary connective
     * @param f1 a <code>Formula</code>
     * @param f2 a <code>Formula</code>
     */
    public Formula(char cntv, Formula f1, Formula f2) {
        this.sign = UNKNOWN;
        this.cntv = cntv;
        this.type = COMP_BINARY;
        this.knowledge = UNKNOWN;
        this.propVar = null;
        this.childList = new ArrayList<Formula>();
        this.childList.add(f1);
        this.childList.add(f2);
        expanded = false;

        if (Character.isDigit(this.cntv) || this.cntv == '*') {     //ion
            this.rank = Math.max(1 + f1.getRank(), f2.getRank());
        } else {
            this.rank = Math.max(f1.getRank(), f2.getRank());
        }

        justPrefix = null;
        qn = NONE;
    }

    /**
     * Constructs a signed <code>Formula</code> given a turnstile and a <code>Formula</code>.
     * Private constructor, only to be used by other constructor.
     * @param sign truth turnstile
     * @param old a <code>Formula</code>
     */
    private Formula(int sign, Formula old) {
        this.sign = sign;

        this.cntv = old.cntv;
        this.type = old.type;
        this.knowledge = old.knowledge;
        this.propVar = old.propVar;
        this.childList = old.childList;
        this.rank = old.rank;
        expanded = false;

        justPrefix = null; //handle with caution
        this.qn = old.qn;
    }

    /**
     * Constructs a signed <code>Formula</code> given a turnstile, knowledge type and a <code>Formula</code>.
     * @param sign truth turnstile
     * @param knowledge type of knowledge in this formula
     * @param old <code>Formula</code>
     */
    private Formula(int sign, int knowledge, Formula old) {
        this(sign, old);
        this.knowledge = knowledge;
    }
    /**
     * Constructs a signed <code>Formula</code> given a turnstile, knowledge type, a <code>Formula</code> and a quantifier.
     * @param sign truth turnstile
     * @param knowledge type of knowledge to store in this formula
     * @param old a <code>Formula</code>
     * @param qn quantifier
     */
    private Formula(int sign, int knowledge, Formula old, int qn) {
        this(sign, knowledge, old);
        this.qn = qn;
    }
    
    /**
     * Constructs a signed <code>Formula</code> given a turnstile, knowledge type, a <code>Formula</code>, a quantifier and a justification prefix.
     * @param sign truth turnstile
     * @param knowledge type of knowledge to store in this formula
     * @param old a <code>Formula</code>
     * @param qn quantifier
     * @param jp justification prefix for this formula
     */
    public Formula(int sign, int knowledge, Formula old, int qn, ArrayList<Justification> jp) {
        this(sign, knowledge, old, qn);
        if (jp != null ) {
            this.justPrefix = new ArrayList<Justification>(jp);
        }
    }

    /**
     * Constructs a signed <code>Formula</code> given a turnstile, knowledge type, a <code>Formula</code> and a justification prefix.
     * @param sign truth turnstile
     * @param knowledge type of knowledge to store in this formula
     * @param old a <code>Formula</code>
     * @param jp justification prefix for this formula
     */
    public Formula(int sign, int knowledge, Formula old, ArrayList<Justification> jp) {
        this(sign, knowledge, old);
        if (jp != null ) {
            this.justPrefix = new ArrayList<Justification>(jp);
        }
    }

    /**
     * Returns the justification prefix of this formula
     * @return a list of <code>Justification</code>
     */
    public ArrayList<Justification> getJPrefix() {
        return justPrefix;
    }
    /**
     * Adds an interpretation symbol to the justification prefix.
     * @param j a <code>Justification</code> to be added.
     */
    public void addJustification(Justification j) {
        if (this.justPrefix == null) {
            this.justPrefix = new ArrayList<Justification>();
        }
        this.justPrefix.add(j);
    }
    /**
     * Returns the quantifier for this canonical justification.
     * @return
     */
    public int getQuantifier() {
        return this.qn;
    }
    /**
     * Sets the quantifier for this canonical justification.
     * @param qn
     */
    public void setQuantifier(int qn) {
        this.qn = qn;
    }
    /**
     * Returns rank of this formula.
     * @return rank
     */
    public int getRank() {
        return rank;
    }
    /**
     * Sets rank for this <code>Formula</code>.
     * @param rank rank of this <code>Formula</code>.
     */
    public void setRank(int rank) {
        this.rank = rank;
    }

    /**
     * Tests whether this formula has been already expanded.
     * @return <code>true</code> if already been expanded
     */
    public boolean isExpanded() {
        return expanded;
    }
    /**
     * Update marker for expansion
     * @param b
     */
    public void setExpanded(boolean b) {
        this.expanded = b;
    }
    /**
     * Returns propositional variable name.
     * @return
     */
    public String getVar() {
        return propVar;
    }
    /**
     * Returns the type of this <code>Formula</code>
     * @return
     */
    public int getType() {
        return this.type;
    }
    /**
     * Sets sign/truth turnstile
     * @param sign a truth turnstile 
     */
    public void setSign(int sign) {
        this.sign = sign;
    }
    /**
     * Returns sign/truth turnstile of this <code>Formula</code>
     * @return
     */
    public int getSign() {
        return sign;
    }
    /**
     * Returns connective
     * @return
     */
    public char getCntv() {
        return this.cntv;
    }
    /**
     * Returns type of knowledge stored in this <code>Formula</code>
     * @return
     */
    public int getKnowledgeType() {
        return this.knowledge;
    }
    /**
     * Sets knowledge type for this <code>Formula</code>
     * @param t
     */
    public void setKnowledgeType(int t) {
        this.knowledge = t;
    }
    /**
     * Returns the i'th child
     * @param i the index of the child to return
     * @return the i'th child of this <code>Formula</code>
     */
    public Formula getChild(int i) {
        if (i < childList.size()) return childList.get(i);
        else {
            //System.out.println("Returning empty child for " + this);
            return null;
        }
    }
    public boolean equals(Formula f) {
        if (this.type != f.type || this.sign != f.sign || this.knowledge != f.knowledge) return false;
        if (this.justPrefix != null) {
            if (f.justPrefix == null || (this.justPrefix.size() != f.justPrefix.size())) return false;
            for (int i = 0; i < this.justPrefix.size(); i++) {
                Justification j1 = this.justPrefix.get(i);
                Justification j2 = f.justPrefix.get(i);
                if (!j1.equals(j2)) return false;
            }
        }
        if (this.type == ATOMIC) return this.propVar.equalsIgnoreCase(f.propVar);
        else if (this.cntv == f.cntv) {
            for (int i = 0; i < this.childList.size(); i++) {
                if (!this.getChild(i).equals(f.getChild(i))) return false;
            }
            return true;
            
        } else return false;
    }
    /**
     * Returns a string representation of this <code>Formula</code>
     * @return string representation of this <code>Formula</code>
     */
    @Override
    public String toString() {
        String s = "";
        String ionSymbols[] = {"♢","♡","♠","O","♣", "•", "∆", "∇", "⋈"};
        //s += "<" + this.rank + "> ";
        if (this.justPrefix != null) {
            for (int i = justPrefix.size() - 1; i >= 0; i--) {
                s += justPrefix.get(i);
            }
            s += " ";
        }

        if (this.knowledge == HARD || this.knowledge == JUST) {
            switch (this.sign) {
                case TRUE: s += "⊨ ";           break;
                case NOT_TRUE: s += "⊭ ";      break;
                case POT_TRUE: s += "⊫ ";      break;
                case NOT_POT_TRUE: s += "⊯ ";   break;
            }
        } else if (this.knowledge == SOFT) {
            switch (this.sign) {
                case TRUE: s += "⊨₅ ";           break;
                case NOT_TRUE: s += "⊭₅ ";      break;
                case POT_TRUE: s += "⊫₅ ";      break;
                case NOT_POT_TRUE: s += "⊯₅ ";   break;
            }
        } /*else if (this.knowledge == JUST) {
            switch (this.sign) {
                case TRUE: s += "+* ";           break;
                case NOT_TRUE: s += "+/* ";      break;
                case POT_TRUE: s += "-/* ";      break;
                case NOT_POT_TRUE: s += "-* ";   break;
            }
        }*/

        if (this.type == ATOMIC) {
            s += this.propVar;
        }
        else if (this.type == COMP_UNARY) {
            if (this.cntv == '#') {
                s += "~'(" + childList.get(0) + ")";
            } else if (this.cntv == '@') {
                s += "bot(" + childList.get(0) + ")";
            } else {
                s += this.cntv + "(" + childList.get(0) + ")";
            }

        }
        else {
            if (this.cntv == '>') {
                s += "(" + childList.get(0).toString() + " -> " + childList.get(1).toString() + ")";
            } else if (Character.isDigit(this.cntv)) {
                s += ionSymbols[this.cntv-'0'] + "(" + childList.get(0).toString() + ", " + childList.get(1).toString() + ")";
            } else if (this.cntv == '*') {
                s += "*(" + childList.get(0).toString() + ", " + childList.get(1).toString() + ")";
            } else {
                s += "(" + childList.get(0).toString() + " " + this.cntv + " " + childList.get(1).toString() + ")";
            }

        }
        if (this.qn == UNIV) s += "∀";
        else if (this.qn == EXIST) s += "∃";
        return s;
    }
}
