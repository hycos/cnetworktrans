package org.snt.cnetworktrans.core;

import org.apache.commons.lang3.StringUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.inmemantlr.tree.Ast;
import org.snt.inmemantlr.tree.AstNode;
import org.snt.inmemantlr.tree.AstProcessor;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public abstract class RegexSplitter extends AstProcessor <String,String> {

    final static Logger logger = LoggerFactory.getLogger(RegexSplitter.class);

    protected Map<String, String> vmap = new HashMap<String, String>();

    private String regexVar = "";

    public static int vid = 0;

    public RegexSplitter(Ast regex) {
        super(regex);
    }


    public String putVar(String val) {
        String var = "v" + vid;
        this.regexVar = var;
        this.vmap.put(var, val);
        vid++;
        return var;
    }

    public String createBinaryExpression(String exp, List<AstNode> nodes) {
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

    public void simpleProp(AstNode n) {

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
        return this.smap.get(this.ast.getRoot());
    }

    @Override
    protected void initialize() {
        for(AstNode n : this.ast.getNodes()){
            this.smap.put(n, "");
        }
    }


    public abstract String getResult();
    public abstract String getVariables();

    public String getInputString() {
        return getVariables() + "\n\n" + getResult();
    }


}
