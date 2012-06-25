/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package ca.uwo.csd.piil;

import java.util.ArrayList;
import java.util.Scanner;
import java.util.StringTokenizer;
import java.util.regex.Pattern;

/**
 * <code>Parser</code> implements a recursive decent parser of sequence of propositional
 * partial information ionic formula of arbitrary rank. The Grammar it implements is the
 * following:
 * <pre>
 * Sequence     ->  Sentence (Separator Sentence)*
 * Sentence     ->  Formula | Turnstile Formula
 * Formula      ->  Propositional_Variable | Unary_con Formula | Formula Binary_Con Formula | Ion | '(' Formula ')' | 'bot(' Formula ')'
 * Ion          ->  '*(' Formula, Formula ')' |   '*' Digit '(' Formula, Formula ')'
 * Unary_Con    ->  - | ~ | ~'
 * Binary_Con   ->  & | | | -> | !
 * Digit        -> [0-8]
 * Propositional_Variable -> [a-zA-Z0-9_]+
 * Precedence of connectives (lowest to highest) : ->, |, &, !, (-,~,~')
 * </pre>
 * @author Syeed Ibn Faiz
 */
public class Parser {

    /**
     * Parses a sequence of sentences of propositional partial information ionic logic.
     * @param str a sequence of logic sentences
     * @return a list of <code>Formula</code>s
     * @throws Exception
     */
    public ArrayList<Formula> parse(String str) throws Exception  {
        ArrayList<Formula> sentList = new ArrayList<Formula>();
        str = preprocess(str);
        StringTokenizer tokenizer = new StringTokenizer(str, ";\n");

        while (tokenizer.hasMoreTokens()) {
            String s = tokenizer.nextToken();
            try {
                Formula f = parseSentence(s);
                f.setKnowledgeType(Formula.HARD);
                sentList.add(f);
            } catch (Exception ex) {
                String msg = ex.getMessage();
                msg += " (while processing " + s + ")";
                throw new Exception(msg);
            }
        }
        return sentList;
    }

    /**
     * Parses a single sentence. True turnstile is assumed if none given.
     * T    means True
     * NT   means Not True
     * PT   means Potentially True
     * NPT  means Not Potentially True
     * @param str a single logic sentence
     * @return
     * @throws Exception
     */
    public Formula parseSentence(String str) throws Exception {
        
        int sign = -1;
        if (str.startsWith("T")) {
            if (str.length() > 1) str = str.substring(1);
            else throw new Exception("Parsing Error. Nothing after T..");
            sign = Formula.TRUE;
        }
        else if (str.startsWith("NT")) {
            if (str.length() > 2) str = str.substring(2);
            else throw new Exception("Parsing Error.  Nothing after NT..");
            sign = Formula.NOT_TRUE;
        }
        else if (str.startsWith("PT")) {
            if (str.length() > 2) str = str.substring(2);
            else throw new Exception("Parsing Error.  Nothing after PT..");
            sign = Formula.POT_TRUE;
        }
        else if (str.startsWith("NPT")) {
            if (str.length() > 3) str = str.substring(3);
            else throw new Exception("Parsing Error.  Nothing after NPT..");
            sign = Formula.NOT_POT_TRUE;
        } else {
            //default case
            sign = Formula.TRUE;
        }

        int index = find(str, '>');
        Formula f = null;
        if (index != -1) {                              //a&b|c > ~d!e
            String str1 = str.substring(0, index);      //a&b|c
            String str2 = str.substring(index + 1);     //~d!e
            
            f = new Formula('>', parseF1(str1, '|'), parseSentence(str2));
        }
        else {
            f = parseF1(str, '|');
        }

        if (sign != -1) f.setSign(sign);
        return f;
    }

    /**
     * Parses a formula which does not contain any connectives with precedence
     * lower than <code>cntv</code> at the top level. This function is written so that it can be
     * used for &, | and !. For each connective it finds its first occurrence.
     * If not found then proceeds with the next connective. Otherwise splits the
     * string into two.
     * @param str
     * @param cntv
     * @return
     * @throws Exception
     */
    private Formula parseF1(String str, char cntv) throws Exception {

        int index = find(str, cntv);
        String str1 = null;
        if (index == -1) {
            str1 = str;
        }
        else {
            str1 = str.substring(0, index);
        }

        Formula f = null;
        switch (cntv) {            
            case '|': f = parseF1(str1, '&');       break;
            case '&': f = parseF1(str1, '!');       break;
            case '!': f = parseF2(str1);            break;
        }
        if (index == -1) return f;

        String str2 = str.substring(index + 1);
        return new Formula(cntv, f, parseF1(str2, cntv));
    }

    /**
     * Parses a formula which does not contain any binary connective at the top level.
     * -, ~ and ~' have equal precedence.
     * @param str
     * @return
     * @throws Exception
     */
    public Formula parseF2(String str) throws Exception {

        if (str.startsWith("-")) {
            if (str.length() > 1) str = str.substring(1);
            else throw new Exception("Parsing Error.  Nothing after -..");
            return new Formula('-', parseF2(str));

        } else if(str.startsWith("~")) {
            if (str.length() > 1) str = str.substring(1);
            else throw new Exception("Parsing Error.  Nothing after ~..");
            return new Formula('~', parseF2(str));

        } else if(str.startsWith("#")) {
            if (str.length() > 1) str = str.substring(1);
            else throw new Exception("Parsing Error.  Nothing after ~'(#)..");
            return new Formula('#', parseF2(str));

        } else if(str.startsWith("bot")) {
            if (str.length() > 3) str = str.substring(3);
            else throw new Exception("Parsing Error.  Nothing after bot..");
            return new Formula('@', parseF3(str));
            
        } else if (str.startsWith("*")) {
            char op = 0;
            if (str.length() > 2 && Character.isDigit(str.charAt(1))) {
                op = str.charAt(1);
                str = str.substring(2);
                
            } else {
                op = '*';
                str = str.substring(1);
            }
            
            if (str.startsWith("(") && str.endsWith(")")) {
                if (str.length() > 1) str = str.substring(1, str.length() - 1);
                else throw new Exception("Parsing Error.  Nothing after bot..");
            } else {
                throw new Exception("Parsing error. () expected");
            }

            int index = find(str, ',');
            Formula f = null;
            if (index != -1) {
                String str1 = str.substring(0, index);
                String str2 = str.substring(index + 1);
                return new Formula(op, parseSentence(str1), parseSentence(str2));

            } else {
                throw new Exception("Parsing error. , expected");
            }            

        } else {
            return parseF3(str);
        }
    }
    /**
     * Parses a formula which is either a propositional formula or has the form
     * '(' Formula ')'.
     * @param str
     * @return
     * @throws Exception
     */
    public Formula parseF3(String str) throws Exception {        
        if (str.startsWith("(")) {
            if (!str.endsWith(")")) {
                throw new Exception("Missing )..");
            }
            /*else {
                if (str.length() > 1) str = str.substring(1, str.length() - 1);
                else throw new Exception("Parsing Error.  Nothing after bot..");
            }*/
            str = str.substring(1, str.length() - 1);
            return parseSentence(str);
        }
        else {
            //proposition variable
            for (int i = 0; i < str.length(); i++) {
                if (!Character.isLetterOrDigit(str.charAt(i)) && str.charAt(i) != '_') {
                    throw  new Exception("Unexpected character in propositional variable name: " + str);
                }
            }
            if (str.isEmpty()) {
                throw  new Exception("Empty operand found ");
            }
            return new Formula(str);
        }
    }

    /**
     * Searches <code>ch</code> in <code>String s</code> outside of any bracket, that means
     * find("(a)", 'a') returns -1
     * @param s a String where to look for <code>ch</code>
     * @param ch a character to find in <code>s</code>
     * @return the index where <code>ch</code> is found or -1 if not found
     */
    public int find(String s, char ch) {
        int bCount = 0;

        for (int i = 0; i < s.length(); i++) {
            if (s.charAt(i) == '(') {
                bCount++;
            }
            else if(s.charAt(i) == ')') {
                bCount--;
            }
            else if(s.charAt(i) == ch && (bCount == 0)) {
                return i;
            }
        }
        return -1;
    }

    /**
     * Preprocesses input string to remove whitespace, convert 2-character
     * connective into 1-character. From
     * -> to >
     * /\ to &
     * \/ to |
     * ~' to #
     * @param str
     * @return
     */
    public String preprocess(String str) {
        str = str.replaceAll("[ \t]+", "");
        str = str.replaceAll("->", ">");
        str = str.replaceAll(Pattern.quote("/\\"), "&");
        str = str.replaceAll(Pattern.quote("\\/"), "|");
        str = str.replaceAll("~'", "#");
        return str;
    }

    /**
     * Main class for testing.
     * @param srgs
     */
    public static void main(String srgs[]) {
        
        Parser parser = new Parser();
        Solver solver = new Solver();
        try {
            while (true) {
                Scanner s = new Scanner(System.in);
                String line = s.nextLine();
                if (line.equalsIgnoreCase("quit")) break;

                ArrayList<Formula> l = parser.parse(line);
                System.out.println(l);
                ArrayList<Interpretation> result = solver.solve(l);
                if (result == null) {
                    System.out.println("No model");
                } else {
                    //System.out.println(result);
                    for (int i = 0; i < result.size(); i++) {
                        System.out.println(result.get(i).toString());
                    }
                    System.out.println("");
                    Ordering ordering = new Ordering(result);
                    result = ordering.getJustificationOrdering();
                    System.out.println("Minimal models according to justification ordering:");
                    for (Interpretation i: result) {
                        System.out.println(i);
                    }
                    result = ordering.getWarrantOrdering();
                    System.out.println("Minimal models according to warrant ordering:");
                    for (Interpretation i: result) {
                        System.out.println(i);
                    }
                }
            }
        } catch (Exception ex) {
            System.out.println(ex.getMessage());
            ex.printStackTrace();
        }
    }
}
