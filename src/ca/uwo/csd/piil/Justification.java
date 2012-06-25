/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package ca.uwo.csd.piil;

/**
 * Justification stores interpretation symbols that constitute
 * justification prefix. The name of this class is a bit ambiguous
 * and may be renamed in future. Possible alternative names are
 * InterpretationSymbol, JustificationSymbol.
 * @author Syeed Ibn Faiz
 */
public class Justification {

    private static int count = 1;   // static counter to generate unique symbol
    private int lbl;                // a particular count value for this symbol
    private int rank;               // rank of this interpretation symbol

    /**
     * Constructs a justification symbol.
     * @param rank rank of this symbol
     * @param isUniv specifies whether this symbol is for a universal quantifier or not.
     */
    public Justification(int rank, boolean isUniv) {
        this.rank = rank;
        if (isUniv) this.lbl = 0;   // this symbol is a variable, unifyable with a symbol
        else this.lbl = count++;    // a concrete symbol
    }

    public Justification(Justification old) {
        this.rank = old.rank;
        this.lbl = old.lbl;
    }
    /**
     * Tests whether this symbol can be unified with a given symbol.
     * @param <code>j</code> an interpretation symbol/variable
     * @return <code>true</code> if the given symbol unifies with this symbol.
     */
    public boolean equals(Justification j) {
        if (this.rank != j.rank) return false;
        return this.lbl == 0 || j.lbl == 0;
    }

    public int getLbl() {
        return lbl;
    }

    public int getRank() {
        return rank;
    }

    
    /**
     * Returns a string representation of this symbol.
     * @return a string representation of this symbol.
     */
    @Override
    public String toString() {
        if (lbl == 0) return "J";
        return "j" + lbl;
    }
}
