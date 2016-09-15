package org.snt.cnetworktrans.lang;

import org.apache.commons.lang3.StringUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.cnetwork.core.*;
import org.snt.cnetworktrans.exceptions.NotSupportedException;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

public abstract class SmtTranslator {

    protected ConstraintNetwork cn = null;
    protected Map<Node, String> vresolv = null;
    protected Map<Node, String> vdecl = null;
    protected Stack<NetworkEntity.NetworkEntityKind> ctx;


    final static Logger logger = LoggerFactory.getLogger(SmtTranslator.class);

    public SmtTranslator() {
        this.vresolv = new HashMap<Node, String>();
        this.vdecl = new HashMap<Node, String>();
        this.ctx = new Stack<NetworkEntity.NetworkEntityKind>();
    }

    public void init() {
        for(Node n : this.cn.vertexSet()) {
            if(n.isLiteral() || n.isRegex() || n.isOperand()) {
                this.vresolv.put(n, n.getLabel());
            }
        }
    }

    protected void doBacktrack(Node n) throws NotSupportedException {
        // we have to do it twice -- some functions need their params
        // to be converted
        backtrack(n);
    }

    protected void ctxPush(Node n) {
        if(n.isOperation())
            this.ctx.push(n.getKind());
    }

    protected void ctxPop(Node n) {
        if(n.isOperation())
            this.ctx.pop();
    }

    protected void backtrack(Node n) throws NotSupportedException {

        ctxPush(n);

        if (n.isRegex()) {
            this.vresolv.put(n, translateRegex(n));
            ctxPop(n);
            return;
        }

        List<Node> pars = this.cn.getParametersFor(n);

        if (pars != null && pars.size() > 0) {
            for(Node par : pars) {
                backtrack(par);
            }
        }


        if (!n.isOperation()) {

            Stack<String> otrans = getOperandTrans(n);
            int otsize = otrans.size();

            if(otsize > 0) {
                String out = "";

                out = otrans.pop();

                if(otsize == 2) {
                    while (!otrans.isEmpty()) {
                        out = "(" + otrans.pop() + " " + out;
                    }
                    out += StringUtils.repeat(")", otsize-1);
                }

                this.vresolv.put(n, out);
            }
            ctxPop(n);
            return;
        }


        Stack<String> strans = getOperationTrans(n);

        int stranssiz = strans.size();
        String out = "";

        while (!strans.isEmpty()) {
            out += "(" + strans.pop() + " ";
        }

        for (Node p : pars) {
            out += vresolv.get(p) + " ";
        }

        out += StringUtils.repeat(")",stranssiz);

        vresolv.put(n, out);
        ctxPop(n);
    }

    protected void debug() {

        logger.info("RESOLVE: =================================\n");
        for (Map.Entry<Node, String> e : vresolv.entrySet()) {
            logger.info(e.getKey().getId() + " :: " + e.getValue());
        }
        logger.info("\n=========================================\n");
    }

    public void setConstraintNetwork(ConstraintNetwork cn) throws NotSupportedException{
        if(!isTranslatable(cn)) {
            throw new NotSupportedException("Constraint Network is not translatable ");
        }
        this.cn = cn;
        init();
    }

    public abstract String translate() throws NotSupportedException;

    public abstract Stack<String> getOperationTrans(Node op) throws NotSupportedException;

    public Stack<String> getOperandTrans(Node op) throws NotSupportedException {

        Stack<String> ret = new Stack<String>();
        assert (op.isOperand());

        if (op.isLiteral() && op.isNumeric()) {
            Operand operand = (Operand) op;

            String lbl = "";
            long max = operand.getRange().getMax();
            if (operand.getRange().getMax() < 0) {
                lbl = "(- " + (-max) + ")";
            } else {
                lbl = String.valueOf(max);
            }
            ret.push(lbl);
            return ret;
        }

        String lbl = vresolv.get(op);

        if(op.isLiteral() && op.isString()) {
            lbl = SmtEscape.trimQuotes(lbl);
            lbl = "\"" +  esc(lbl) + "\"";
        }

        ret.push(lbl);
        return ret;
    }


    protected abstract boolean notTranslatable(Operation op);

    public boolean isTranslatable(ConstraintNetwork cn) {
        for(Node n : cn.vertexSet()) {
            if(n.isOperation()) {
                if(notTranslatable((Operation)n)) {
                    logger.info("op " + n.getKind());
                    return false;
                }
            }
        }
        return true;
    }

    protected abstract String translateRegex(Node regex);

    protected abstract String esc(String s);

}
