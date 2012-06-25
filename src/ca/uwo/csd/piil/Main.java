/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package ca.uwo.csd.piil;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;

/**
 * Main class. It performs the following steps.
 * <ul>
 * <li>Get content from input file.</li>
 * <li>Remove comments from content.</li>
 * <li>Use <code>Parser</code> to parse content and get a list of <code>Formula</code>s from that.</li>
 * <li>Use <code>Solver</code> to get a list of interpretation schemes from the list of <code>Formula</code>s.</li>
 * <li>Write the set of interpretation schemes to output file/standard output.</li>
 * </ul>
 * @author Syeed Ibn Faiz
 */
public class Main {

    public static void main(String args[]) {
        if (args.length < 1) {
            System.out.println("Usage java -jar pil.jar inputFile [outputFile]");
            return;
        }

        File inputFile = new File(args[0]);
        File outputFile = null;
        if (args.length > 1) {
            outputFile = new File(args[1]);
        }

        String content = "";
        try {
            BufferedReader reader = new BufferedReader(new FileReader(inputFile));
            String s = "";
            while ((s = reader.readLine()) != null) {
                content += s + "\n";
            }
            reader.close();
        } catch (IOException ex) {
            System.out.println("Error occured while reading from input file: " + ex.getMessage());
            System.exit(0);
        }

        content = processComment(content);
        //System.out.println(content);

        Parser parser = new Parser();
        Solver solver = new Solver();
        ArrayList<Interpretation> result = null;
        ArrayList<Formula> fList = null;
        try {
            fList = parser.parse(content);
            result = solver.solve(fList);
        } catch (Exception ex) {
            System.out.println("Exception occured : " + ex.getMessage());
            System.exit(0);
        }

        try {
            BufferedWriter writer;
            if (outputFile != null) {
                writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(outputFile), "UTF-16"));
            } else {
                writer = new BufferedWriter(new OutputStreamWriter(System.out, "UTF-16"));
            }

            if (fList != null) {
                writer.write("Input: " + fList.toString() + "\n\n");
            }
            if (result == null) {
                writer.write("No model found.");
            } else {
                if (result.size() == 1) {
                    writer.write("1 model found.\n");
                } else {
                    writer.write(result.size() + " models found.\n");
                }

                for (int i = 0; i < result.size(); i++) {
                    writer.write(result.get(i).toString());
                    writer.write("\n");
                }

                Ordering ordering = new Ordering(result);
                result = ordering.getJustificationOrdering();
                writer.write("Minimal models according to justification ordering:\n");
                for (Interpretation i : result) {
                    writer.write(i.toString());
                }
                result = ordering.getWarrantOrdering();
                writer.write("\nMinimal models according to warrant ordering:\n");
                for (Interpretation i : result) {
                    writer.write(i.toString());
                }
            }
            writer.flush();
            writer.close();
        } catch (IOException ex) {
            System.out.println("Exception occured while writing to output file: " + ex.getMessage());
            System.exit(0);
        }

        System.out.println("Done.");
    }

    /**
     * Removes comment from a given input.
     * @param s
     * @return
     */
    public static String processComment(String s) {
        int start;
        while ((start = s.indexOf("/*")) != -1) {
            int end = s.indexOf("*/", start + 1);
            if (end == -1) {
                break;
            }
            s = s.replace(s.substring(start, end + 2), "");
        }
        return s;
    }
}
