package org.snt.cnetworktrans.lang.sol;

import org.snt.cnetwork.core.Node;
import org.snt.cnetwork.core.Operation;
import org.snt.cnetworktrans.exceptions.NotSupportedException;
import org.snt.cnetworktrans.lang.SmtTranslator;

import java.util.Stack;


public class SolTranslator extends SmtTranslator {


    @Override
    public String translate() throws NotSupportedException {
        return this.cn.getConstraintNetwork().toConfig();
    }

    @Override
    public Stack<String> getOperationTrans(Node op) {
        return new Stack<>();
    }

    @Override
    protected boolean notTranslatable(Operation op) {
        return false;
    }


    @Override
    protected String translateRegex(Node regex) {
        return "";
    }

    @Override
    protected String esc(String s) {
        return s;
    }
}
