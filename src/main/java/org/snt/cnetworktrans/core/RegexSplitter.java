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

package org.snt.cnetworktrans.core;

import org.apache.commons.lang3.StringUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.inmemantlr.tree.ParseTree;
import org.snt.inmemantlr.tree.ParseTreeNode;
import org.snt.inmemantlr.tree.ParseTreeProcessor;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public abstract class RegexSplitter extends ParseTreeProcessor <String,String> {

    final static Logger LOGGER = LoggerFactory.getLogger(RegexSplitter.class);

    protected Map<String, String> vmap = new HashMap<String, String>();

    private String regexVar = "";

    public static int vid = 0;

    public RegexSplitter(ParseTree regex) {
        super(regex);
    }


    public String putVar(String val) {
        String var = "v" + vid;
        this.regexVar = var;
        this.vmap.put(var, val);
        vid++;
        return var;
    }

    public String createBinaryExpression(String exp, List<ParseTreeNode>
            nodes) {
        String out = "";

        if(nodes.size() > 1) {
            for (int i = 0; i <= nodes.size()-2; i++) {
                out += " (" + exp + " " + smap.get(nodes.get(i));
            }
            out += " " + smap.get(nodes.get(nodes.size()-1));
            out += StringUtils.repeat(")", nodes.size() - 1);
        } else if (nodes.size() == 1){
            out = smap.get(nodes.get(0));
        }
        return out;
    }

    public void simpleProp(ParseTreeNode n) {

        String s = "";
        if (n.getChildren().size() == 0) {
            smap.put(n, "\"" + n.getEscapedLabel() + "\"");
        } else {
            assert (n.getChildren().size() == 1);
            smap.replace(n, smap.get(n.getChildren().get(0)));
        }
    }

    public String getRegexVar() {
        return this.regexVar;
    }

    public String getRootEntry() {
        return this.smap.get(this.parseTree.getRoot());
    }

    @Override
    protected void initialize() {
        for(ParseTreeNode n : this.parseTree.getNodes()){
            this.smap.put(n, "");
        }
    }


    public abstract String getResult();
    public abstract String getVariables();

    public String getInputString() {
        return getVariables() + "\n\n" + getResult();
    }


}
