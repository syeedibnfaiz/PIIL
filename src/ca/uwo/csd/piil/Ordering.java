/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package ca.uwo.csd.piil;

import java.util.ArrayList;

/**
 *
 * @author Syeed Ibn Faiz
 */
public class Ordering {

    ArrayList<Interpretation> models;
    ArrayList<ArrayList<Formula>> posJust;
    ArrayList<ArrayList<Formula>> negJust;

    public Ordering(ArrayList<Interpretation> models) {
        this.models = models;
        if (models != null) {
            posJust = new ArrayList<ArrayList<Formula>>();
            negJust = new ArrayList<ArrayList<Formula>>();
            for (Interpretation i : models) {
                ArrayList<Formula> justK = i.getJustKnowledge();                

                ArrayList<Formula> pos = new ArrayList<Formula>();
                ArrayList<Formula> neg = new ArrayList<Formula>();

                for (Formula f : justK) {
                    if (f.getSign() == Formula.TRUE || f.getSign() == Formula.POT_TRUE) {
                        pos.add(f);
                    } else {
                        neg.add(f);
                    }
                }

                posJust.add(pos);
                negJust.add(neg);
            }
            for (int i = 0; i < models.size(); i++) {
                ArrayList<Formula> hardK = models.get(i).getHardKnowledge();

                for (Formula f : hardK) {
                    if (f.getSign() == Formula.TRUE || f.getSign() == Formula.POT_TRUE) {
                        //pos.add(f);
                        for (int m = 0; m < posJust.size(); m++) {
                            int sz = posJust.get(m).size();
                            for (int n = 0; n < sz; n++) {
                                if (isEqual(f, posJust.get(m).get(n))) {
                                    posJust.get(i).add(f);
                                }
                            }
                        }
                    } else {
                        //neg.add(f);
                        for (int m = 0; m < negJust.size(); m++) {
                            int sz = negJust.get(m).size();
                            for (int n = 0; n < sz; n++) {
                                if (isEqual(f, negJust.get(m).get(n))) {
                                    negJust.get(i).add(f);
                                }
                            }
                        }
                    }
                }

                //posJust.add(pos);
                //negJust.add(neg);
            }
        }
    }

    public ArrayList<Interpretation> getJustificationOrdering() {
        ArrayList<Interpretation> minModels = new ArrayList<Interpretation>();
        if (models == null) return minModels;
        
        for (int i = 0; i < models.size(); i++) {
            boolean minimal = true;
            for (int j = 0; j < models.size(); j++) {
                if (i == j) continue;
                // j < i?                
                if (precedesJust(j, i) && !precedesJust(i, j)) {
                    minimal = false;                    
                    break;
                }
            }
            if (minimal) {
                //System.out.println("Minimal model: " + models.get(i));
                minModels.add(models.get(i));
            }
        }
        return minModels;
    }
    public ArrayList<Interpretation> getWarrantOrdering() {
        ArrayList<Interpretation> minModels = new ArrayList<Interpretation>();
        if (models == null) return minModels;

        for (int i = 0; i < models.size(); i++) {
            boolean minimal = true;
            for (int j = 0; j < models.size(); j++) {
                if (i == j) continue;
                // j < i?
                if (precedesWarrant(j, i) && !precedesWarrant(i, j)) {
                    minimal = false;
                    break;
                }
            }
            if (minimal) {
                //System.out.println("Minimal warrant model: " + models.get(i));
                minModels.add(models.get(i));
            }
        }
        return minModels;
    }

    private boolean precedesJust(int i, int j) {
        boolean flg = true;
        for (int k = 0; k < posJust.get(j).size(); k++) {
            if (!isMember(posJust.get(j).get(k), posJust.get(i))) {
                flg = false;
                break;
            }
        }
        if (flg) {
            for (int k = 0; k < negJust.get(i).size(); k++) {
                if (!isMember(negJust.get(i).get(k), negJust.get(j))) {
                    flg = false;
                    break;
                }
            }
        }
        if (flg) {
            return true;
        }
        return false;
    }
    private boolean precedesWarrant(int i, int j) {
        if (precedesJust(i, j)) {
            //System.out.println("Here @ " + i + " , " + j);
            ArrayList<Formula> hardKi = models.get(i).getHardKnowledge();
            ArrayList<Formula> hardKj = models.get(j).getHardKnowledge();
            
            for (Formula f : hardKi) {
                if (!isSignedMember(f, hardKj)) return false;
                //else System.out.println(f + " is member of " + hardKj);
            }

            ArrayList<Formula> softKi = models.get(i).getSoftKnowledge();
            ArrayList<Formula> softKj = models.get(j).getSoftKnowledge();

            for (Formula f : softKj) {
                if (!isSignedMember(f, softKi)) return false;
                //else System.out.println(f + " is member of " + softKi);
            }
            return true;
            
        } else {            
            return false;
        }

    }
    private boolean isMember(Formula f, ArrayList<Formula> list) {
        if (list == null) return false;
        for (int i = 0; i < list.size(); i++) {
            if (isEqual(f, list.get(i))) return true;
        }
        return false;
    }

    private boolean isEqual(Formula f1, Formula f2) {
        if (f1.getType() != f2.getType()) return false;
        else if (f1.getType() == Formula.ATOMIC) return f1.getVar().equalsIgnoreCase(f2.getVar());
        else if (f1.getCntv() == f2.getCntv()) {
            if (f1.getType() == Formula.COMP_UNARY) return isEqual(f1.getChild(0), f2.getChild(0));
            else return isEqual(f1.getChild(0), f2.getChild(0)) && isEqual(f1.getChild(1), f2.getChild(1));

        } else return false;        
    }
    private boolean isSignedEqual(Formula f1, Formula f2) {
        if ((f1.getType() != f2.getType()) || (f1.getSign() != f2.getSign())) return false;
        else if (f1.getType() == Formula.ATOMIC) return f1.getVar().equalsIgnoreCase(f2.getVar());
        else if (f1.getCntv() == f2.getCntv()) {
            if (f1.getType() == Formula.COMP_UNARY) return isSignedEqual(f1.getChild(0), f2.getChild(0));
            else return isSignedEqual(f1.getChild(0), f2.getChild(0)) && isSignedEqual(f1.getChild(1), f2.getChild(1));

        } else return false;        
    }
    private boolean isSignedMember(Formula f, ArrayList<Formula> list) {
        if (list == null) return false;
        for (int i = 0; i < list.size(); i++) {
            if (isSignedEqual(f, list.get(i))) return true;
        }
        return false;
    }

}
