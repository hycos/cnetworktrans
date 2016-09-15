package org.snt.cnetworktrans.core;


import org.snt.cnetworktrans.lang.SmtTranslator;
import org.snt.cnetworktrans.lang.cvc4.CVC4Translator;
import org.snt.cnetworktrans.lang.s3.S3Translator;
import org.snt.cnetworktrans.lang.sol.SolTranslator;
import org.snt.cnetworktrans.lang.z3.Z3Translator;

public enum OutputFormat {

    SOL(0, "Sol"),
    CVC4 (1, "CVC4"),
    Z3STR2(2, "Z3Str2"),
    S3(3, "S3");


    private int id;
    private String name;
    private String grammar;

    OutputFormat(int id, String name) {
        this.id = id;
        this.name = name;
    }

    public SmtTranslator getTranslator() {
        switch (this) {
            case SOL: return new SolTranslator();
            case CVC4: return new CVC4Translator();
            case Z3STR2: return new Z3Translator();
            case S3: return new S3Translator();
        }
        return null;
    }

    public String getName() {
        return this.name;
    }

    public static OutputFormat getFormat(String desc) {
        switch(desc) {
            case "sol" : return SOL;
            case "cvc4" : return CVC4;
            case "z3str2": return Z3STR2;
            case "s3" : return S3;
        }
        return null;
    }

    public static String getAvailableFormats() {
        return "(" + SOL.getName() + "," + CVC4.getName() + "," + Z3STR2.getName() + "," + S3.getName() +")";
    }



}
