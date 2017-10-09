package org.snt.cnetworktrans.core;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.inmemantlr.GenericParser;
import org.snt.inmemantlr.exceptions.CompilationException;
import org.snt.inmemantlr.exceptions.IllegalWorkflowException;
import org.snt.inmemantlr.exceptions.ParsingException;
import org.snt.inmemantlr.listener.DefaultTreeListener;
import org.snt.inmemantlr.tree.ParseTree;
import org.snt.inmemantlr.utils.FileUtils;

import java.io.InputStream;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

;


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

    public static ParseTree parse(String regex)  {


        GenericParser gp = new GenericParser(grammar);

        DefaultTreeListener rl = new DefaultTreeListener(s -> filter.contains(s));
        gp.setListener(rl);

        try {
            gp.compile();
        } catch (CompilationException e) {
            assert false; // should never ever happen
        }
        LOGGER.info("Parse regex " + regex);

        try {
            gp.parse(regex);
        } catch (IllegalWorkflowException e) {
            LOGGER.error("error parsing regular expression");
            System.exit(-1);
        } catch (ParsingException e) {
            LOGGER.error("error parsing regular expression");
            System.exit(-1);
        }
        return rl.getParseTree();
    }

}
