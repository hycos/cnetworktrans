package org.snt.cnetworktrans.lang.cvc4;

import org.apache.commons.lang3.StringUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.cnetworktrans.core.RegexSplitter;
import org.snt.inmemantlr.tree.Ast;
import org.snt.inmemantlr.tree.AstNode;

import java.util.regex.Matcher;
import java.util.regex.Pattern;


public class CVC4RegexSplitter extends RegexSplitter {

    final static Logger logger = LoggerFactory.getLogger(CVC4RegexSplitter.class);

    private static String CONCAT = "re.++";
    private static String PLUS = "re.+";
    private static String UNION = "re.union";
    private static String STAR = "re.*";
    private static String MEMBERSHIP = "str.in.re";
    private static String CONV = "str.to.re";
    private static String EQ = "=";
    private static String RANGE = "re.range";
    private static String OPT = "re.opt";
    private static String ALLCHAR = "re.allchar";

    public CVC4RegexSplitter(Ast regex) {
        super(regex);
    }


    @Override
    protected void process(AstNode n) {

        logger.info("Handle " + n.getId() + " " + n.getRule());

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
                for (AstNode c : n.getChildren()) {
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

                    AstNode last = n.getChildren().get(1);
                    AstNode first = n.getChildren().get(0);

                    logger.info("FIRST " + first.getEscapedLabel() + ">> " + first.getId() + " " + smap.get(first));
                    logger.info("LAST " + last.getEscapedLabel() + ">> " + last.getId() + " " + smap.get(last));

                    if (last != null && last.getRule().equals("quantifier")) {
                        switch (last.getLabel()) {
                            case "*":
                                String star = "(" + STAR + " " + smap.get(first) + " )";
                                //String starvar = putVar(star);
                                //smap.put(n, starvar);
                                smap.put(n,star);
                                break;
                            case "+":
                                String plus = "(" + PLUS + " " + smap.get(first) + " )";
                                smap.put(n,plus);
                                break;
                            case "?":
                                String opt = "(" + OPT + " " + smap.get(first) + " )";
                                smap.put(n,opt);
                                break;
                        }

                        int min = -1;
                        int max = -1;
                        Pattern pattern = Pattern.compile("\\{([0-9]*),?([0-9]*)\\}");
                        Matcher matcher = pattern.matcher(last.getLabel());


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
                            logger.info("min " + min + " max" + max);
                        }
                    }
                }

                break;
            case "number":
            case "letter":
            case "literal":
            case "cc_literal":
            case "shared_literal":
                String label = " (" + CONV + " " + "\"" + esc(n.getLabel()) + "\")";
                this.smap.put(n,label);
                break;
            case "atom":
                if(n.isLeaf()) {
                    if(n.getLabel().equals(".")) {
                        smap.put(n, ALLCHAR);
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
                    AstNode first = n.getChildren().get(0);
                    AstNode last = n.getChildren().get(1);
                    String rex = "(" + RANGE + " \"" + esc(first.getLabel()) + "\" \"" + esc(last.getLabel()) + "\")";
                    smap.put(n, rex);
                }
                break;
            case "character_class":
                if (n.getChildren().size() == 1) {
                    simpleProp(n);
                } else {
                    String cc = "";
                    int i = 0;
                    for(i = 0; i < n.getChildren().size() - 1; i++) {
                        AstNode c = n.getChildren().get(i);
                        cc += " (" + UNION + " " + this.smap.get(c);
                    }
                    cc += " " + this.smap.get(n.getChildren().get(i));
                    cc += StringUtils.repeat(")", n.getChildren().size()-1);
                    smap.put(n, cc);
                }
                break;
        }

        //LOGGER.info(debug());
    }

    private String esc(String s) {
        return CVC4Escape.escapeSpecialCharacters(s);
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
