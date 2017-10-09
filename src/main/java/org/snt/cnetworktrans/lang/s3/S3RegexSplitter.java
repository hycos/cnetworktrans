/*
 * cnetworktrans - translate constraint network to various output formats
 * Copyright (C) 2017 Julian Thome <julian.thome.de@gmail.com>
 *
 * cnetworktrans is licensed under the EUPL, Version 1.1 or – as soon
 * they will be approved by the European Commission - subsequent versions of the
 * EUPL (the "Licence"); You may not use this work except in compliance with the
 * Licence. You may obtain a copy of the Licence at:
 *
 * https://joinup.ec.europa.eu/sites/default/files/eupl1.1.-licence-en_0.pdf
 *
 * Unless required by applicable law or agreed to in writing, software distributed
 * under the Licence is distributed on an "AS IS" basis, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied.  See the Licence for the
 * specific language governing permissions and limitations under the Licence.
 */

package org.snt.cnetworktrans.lang.s3;

import org.apache.commons.lang3.StringUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.cnetworktrans.core.RegexSplitter;
import org.snt.inmemantlr.tree.ParseTree;
import org.snt.inmemantlr.tree.ParseTreeNode;

import java.util.regex.Matcher;
import java.util.regex.Pattern;


public class S3RegexSplitter extends RegexSplitter {

    final static Logger LOGGER = LoggerFactory.getLogger(S3RegexSplitter.class);

    private static String CONCAT = "Concat";
    private static String UNION = "Union";
    private static String STAR = "Star";
    private static String MEMBERSHIP = "In";
    private static String EQ = "=";

    private boolean addAny = false;

    public S3RegexSplitter(ParseTree regex) {
        super(regex);
    }


    public String getAny() {

        String any = "" ;
        char from = 'a';
        char to = 'z';
        for (char p = from; p < to; p ++) {
            any += " (" +  UNION  + " \"" + p + "\"";
        }

        any += " \"" + to + "\"";
        any += StringUtils.repeat(")", to-from);
        return any;
    }


    @Override
    protected void process(ParseTreeNode n) {

        LOGGER.info("Handle " + n.getId() + " " + n.getRule());

        switch (n.getRule()) {

            case "root":
                simpleProp(n);
                break;
            case "alternation":
                if (n.getChildren().size() == 1) {
                    simpleProp(n);
                    break;
                }
                String alt = createBinaryExpression(UNION, n.getChildren());
                //alt = "(assert (" + MEMBERSHIP + " v" + vid + " " + alt + " ))";
                //String salt = putVar(alt);
                smap.put(n, alt);
                break;
            case "expr":
                if (n.getChildren().size() == 1) {
                    simpleProp(n);
                    break;
                }
                boolean concat = true;
                for (ParseTreeNode c : n.getChildren()) {
                    if (!c.getRule().equals("element")) {
                        concat = false;
                    }
                }
                if (concat) {
                    String sconcat = createBinaryExpression(CONCAT, n.getChildren());
                    //sconcat = "(assert (" + MEMBERSHIP + " v" + vid + " " + sconcat + "))";
                    //String sexpr = putVar(sconcat);
                    smap.put(n, sconcat);
                }
                break;
            case "element":

                if (n.getChildren().size() == 1) {
                    simpleProp(n);
                } else if (n.getChildren().size() == 2) {

                    ParseTreeNode last = n.getChildren().get(1);
                    ParseTreeNode first = n.getChildren().get(0);

                    String lbl = last.getLabel();


                    if (last != null && last.getRule().equals("quantifier")) {
                        switch (lbl) {
                            case "*":
                                String star = "(" + STAR + " " + smap.get(first) + " )";
                                //String starvar = putVar(star);
                                //smap.put(n, starvar);
                                smap.put(n,star);
                                break;
                            case "+":
                                String plus = "(" + CONCAT + " " +
                                        smap.get(first) + "(" + STAR + " " + smap.get(first) + " ))";
                                //plus = "(assert (= v" + vid + " (" + CONCAT + " " + smap.get(first) + " " + plus + ")))";
                                //String plusvar = putVar(plus);
                                smap.put(n, plus);
                                break;
                            case "?":
                                lbl = "{0,1}";
                                break;
                        }

                        int min = -1;
                        int max = -1;
                        Pattern pattern = Pattern.compile("\\{([0-9]*),?([0-9]*)\\}");
                        Matcher matcher = pattern.matcher(lbl);

                        if (matcher.matches()) {
                            if (matcher.group(1) != null) {
                                min = Integer.parseInt(matcher.group(1));
                            }
                            if (matcher.group(2) != null) {
                                max = Integer.parseInt(matcher.group(2));
                            }


                            String smin = "";
                            String sran = "";

                            if (min > 0) {
                                for (int i = 1; i < min; i++) {
                                    smin += " (" + CONCAT + " " + smap.get(first);
                                }
                                smin += " " + smap.get(first);
                                smin += StringUtils.repeat(")", min - 1);
                            } else if (min <= 0) {
                                smin += "\"\"";
                            }


                            if (max > -1) {

                                String unroll = smin;
                                for (int i = min; i < max; i++) {
                                    sran += " (" + UNION + " " + unroll;
                                    unroll = " (" + CONCAT + " " + this.smap.get(first) + "  " + unroll + ")";
                                }
                                sran += " " + unroll;
                                sran += StringUtils.repeat(")", max - min);
                            } else if (max <= 0) {
                                sran = " (" + CONCAT + " " + smin + " (Star " + smin + "))";
                            }


                            //String result = "(assert (" + MEMBERSHIP + " v" + vid + sran + "))";
                            //String var = putVar(result);

                            //smap.put(n, var);

                            smap.put(n, sran);
                            LOGGER.info("min " + min + " max" + max);
                        }
                    }
                }

                break;
            case "number":
            case "letter":
            case "literal":
            case "cc_literal":
            case "shared_literal":
                String label = "\"" + esc(n.getLabel()) + "\"";
                this.smap.put(n,label);
                break;
            case "atom":
                if(n.isLeaf()) {
                    if(n.getLabel().equals(".")) {
                        smap.put(n, getAny());
                    }
                } else {
                    simpleProp(n);
                }
                break;
            case "cc_atom":
                if (n.getChildren().size() == 0) {
                    ;
                } else if (n.getChildren().size() == 1) {
                    simpleProp(n);
                } else {
                    assert(n.getChildren().size() == 2);

                    char first = n.getChildren().get(0).getLabel().charAt(0);
                    char second = n.getChildren().get(1).getLabel().charAt(0);


                    assert (second >= first);
                    String ran = "";
                    char t = first;
                    for (t = first; t < second; t++) {
                        ran += " (" + UNION + " \"" + t + "\"";
                    }
                    ran += " \"" + t + "\"";
                    ran += StringUtils.repeat(")", second - first);

                    //ran = "(assert (= v" + vid + ran + "))";
                    //String var = putVar(ran);
                    smap.put(n, ran);
                }
                break;
            case "character_class":
                if (n.getChildren().size() == 1) {
                    simpleProp(n);
                } else {
                    String cc = "";
                    int i = 0;
                    for(i = 0; i < n.getChildren().size() - 1; i++) {
                        ParseTreeNode c = n.getChildren().get(i);
                        cc += " (" + UNION + " " + this.smap.get(c);
                    }
                    cc += " " + this.smap.get(n.getChildren().get(i));
                    cc += StringUtils.repeat(")", n.getChildren().size()-1);
                    smap.put(n, cc);
                }
                break;
        }
        LOGGER.info(debug());
    }

    private String esc(String s) {
        return S3Escape.escapeSpecialCharacters(s);
    }


    @Override
    public String getResult() {
        return getRootEntry();
    }

    @Override
    public String getVariables() {
        return "";
    }

}
