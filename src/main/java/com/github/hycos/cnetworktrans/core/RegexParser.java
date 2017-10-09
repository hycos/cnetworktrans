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

package com.github.hycos.cnetworktrans.core;

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
