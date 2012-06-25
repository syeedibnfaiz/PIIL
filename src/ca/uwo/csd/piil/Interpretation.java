/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package ca.uwo.csd.piil;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;

/**
 * Interpretation is a data structure for storing an interpretation scheme.
 * @author Syeed Ibn Faiz
 */
public class Interpretation {

    ArrayList<Formula> hardKnowledge;
    ArrayList<Formula> softKnowledge;
    ArrayList<Formula> justKnowledge;

    /**
     * Constructs an interpretation from a given list of formulas. These formulas
     * constitute an open branch of a tableau.
     * @param l list of formulas.
     */
    public Interpretation(ArrayList<Formula> l) {
        hardKnowledge = new ArrayList<Formula>();
        softKnowledge = new ArrayList<Formula>();
        justKnowledge = new ArrayList<Formula>();

        for(Formula f : l) {
           if (f.getKnowledgeType() == Formula.HARD) {
                hardKnowledge.add(f);
           }
           else if(f.getKnowledgeType() == Formula.SOFT) {
                softKnowledge.add(f);
           }
           else {
               String s = f.toString();               
               justKnowledge.add(f);
           }
        }
        // sorts to remove the duplicates later on
        Comparator<Formula> comp = new Comparator<Formula>() {
            public int compare(Formula o1, Formula o2) {
                String s1 = o1.getVar();
                String s2 = o2.getVar();
                if (s1 == null) return 1;
                else if (s2 == null) return 1;
                else return s1.compareToIgnoreCase(s2);
            }
        };
        Collections.sort(hardKnowledge, comp);
        Collections.sort(softKnowledge, comp);
        Collections.sort(justKnowledge, comp);
    }

    /**
     * Returns a string representation of this interpretation.
     * @return
     */
    @Override
    public String toString() {
        String s = "<";
        s += "{";
        boolean first = true;
        for (int i = 0; i < hardKnowledge.size(); i++) {
            Formula f = hardKnowledge.get(i);
            if (i > 0 && f.getVar().equalsIgnoreCase(hardKnowledge.get(i - 1).getVar())) { //checking for duplicate entries
                continue;
            }
            if (first) first = false;
            else s += ",";

            s += f;
        }        
        s += "},";
        
        s += " {";
        first = true;
        for (int i = 0; i < justKnowledge.size(); i++) {
            Formula f = justKnowledge.get(i);
            if (i > 0 && f.equals(justKnowledge.get(i - 1))) {
                continue;
            }
            if (first) first = false;
            else s += ",";

            String tmp = f.toString();
            if (f.getQuantifier() == Formula.GENJUST) {
                tmp = tmp.replaceAll("⊨", "+*");
                tmp = tmp.replaceAll("⊭", "+/*");
                tmp = tmp.replaceAll("⊫", "-/*");
                tmp = tmp.replaceAll("⊯", "-*");
            }
            s += tmp;
        }
        s += "},";

        s += " {";
        first = true;
        for (int i = 0; i < softKnowledge.size(); i++) {
            Formula f = softKnowledge.get(i);
            if (i > 0 && f.getVar().equalsIgnoreCase(softKnowledge.get(i - 1).getVar())) {
                continue;
            }
            if (first) first = false;
            else s += ",";
            
            s += f;
        }
        s += "}>";

        return s;
    }

    public ArrayList<Formula> getJustKnowledge() {
        return justKnowledge;
    }

    public ArrayList<Formula> getHardKnowledge() {
        return hardKnowledge;
    }

    public ArrayList<Formula> getSoftKnowledge() {
        return softKnowledge;
    }
    
}
