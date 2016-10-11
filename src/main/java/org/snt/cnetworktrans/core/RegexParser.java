package org.snt.cnetworktrans.core;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.inmemantlr.DefaultTreeListener;
import org.snt.inmemantlr.GenericParser;
import org.snt.inmemantlr.exceptions.IllegalWorkflowException;
import org.snt.inmemantlr.tree.Ast;
import org.snt.inmemantlr.utils.FileUtils;;

import java.io.InputStream;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;


public class RegexParser {

    final static Logger LOGGER = LoggerFactory.getLogger(RegexParser.class);


    private static Set<String> filter  = new HashSet<String>(Arrays.asList(new String []{ "alternation", "expr", "literal",
            "quantifier", "atom", "letter", "number", "element",
            "character_class", "cc_atom", "cc_literal"
    }));


    private static String grammar = null;

    public RegexParser() {

        if(grammar == null) {
            ClassLoader classLoader = getClass().getClassLoader();
            InputStream is = classLoader.getResourceAsStream("Regex.g4");
            grammar = FileUtils.getStringFromStream(is);
        }
    }

    public static Ast parse(String regex) {


        GenericParser gp = new GenericParser(grammar, "Regex");

        DefaultTreeListener rl = new DefaultTreeListener(s -> filter.contains(s));
        gp.setListener(rl);

        gp.compile();
        LOGGER.info("Parse regex " + regex);

        try {
            gp.parse(regex);
        } catch (IllegalWorkflowException e) {
            LOGGER.error("error parsing regular expression");
            System.exit(-1);
        }
        return rl.getAst();
    }

}
