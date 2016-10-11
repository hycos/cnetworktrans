import org.junit.Before;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.cnetwork.core.*;
import org.snt.cnetworktrans.core.OutputFormat;
import org.snt.cnetworktrans.core.RegexParser;
import org.snt.cnetworktrans.exceptions.NotSupportedException;
import org.snt.cnetworktrans.lang.SmtEscape;
import org.snt.cnetworktrans.lang.SmtTranslator;
import org.snt.cnetworktrans.lang.cvc4.CVC4Escape;
import org.snt.cnetworktrans.lang.cvc4.CVC4RegexSplitter;
import org.snt.cnetworktrans.lang.s3.S3RegexSplitter;
import org.snt.cnetworktrans.lang.z3.Z3RegexSplitter;
import org.snt.inmemantlr.tree.Ast;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class TestTranslators {

    final static Logger LOGGER = LoggerFactory.getLogger(TestTranslators.class);


    private static ConstraintNetwork cn = null;

    @Before
    public void setUp() throws Exception {
        cn = new ConstraintNetwork();

        Operand a = new Operand("a", OperandKind.NUMVAR);
        Operand b = new Operand("b", OperandKind.NUMVAR);
        Operand c = new Operand("20", OperandKind.NUMLIT);

        Operation add = cn.addOperation(OperationKind.ADD,a,b);
        Operation smeq = cn.addConstraint(OperationKind.SMALLEREQ, add, c);


        Operand s = new Operand("s1", OperandKind.STRVAR);
        Operand ip = new Operand("a*", OperandKind.STRREXP);

        Operation matches = cn.addConstraint(OperationKind.MATCHES, s, ip);

        Operation len = cn.addOperation(OperationKind.LEN,s);

        Operation lencon = cn.addConstraint(OperationKind.GREATEREQ, len, c);

        Operation conv = cn.addOperation(OperationKind.TOSTR, a);

        Operation matches2 = cn.addConstraint(OperationKind.MATCHES, s, conv);
    }


    @Test
    public void testZ3() {


        LOGGER.info("Test Z3");
        SmtTranslator sa = OutputFormat.Z3STR2.getTranslator();
        try {
            sa.setConstraintNetwork(cn);
        } catch (NotSupportedException e) {
            assert(true);
        }
        /**String out = null;
        try {
            out = sa.translate();
        } catch (NotSupportedException e) {
            e.printStackTrace();
        }**/

        //LOGGER.info(out);
    }

    @Test
    public void testS3() {

        ConstraintNetwork simple = new ConstraintNetwork();

        Operand a = new Operand("a", OperandKind.STRVAR);
        Operand b = new Operand("b", OperandKind.STRVAR);

        Operation add = simple.addConstraint(OperationKind.NEQUALS,a,b);

        LOGGER.info("Test S3");
        SmtTranslator sa = OutputFormat.S3.getTranslator();
        try {
            sa.setConstraintNetwork(simple);
        } catch (NotSupportedException e) {
            assert(false);
        }
        String out = null;
        try {
            out = sa.translate();
        } catch (NotSupportedException e) {
            e.printStackTrace();
        }

        LOGGER.info(out);

    }

    @Test
    public void testCVC4() {

        LOGGER.info("Test CVC4");
        SmtTranslator sa = OutputFormat.CVC4.getTranslator();
        try {
            sa.setConstraintNetwork(cn);
        } catch (NotSupportedException e) {
            e.printStackTrace();
        }
        String out = null;
        try {
            out = sa.translate();
        } catch (NotSupportedException e) {
            e.printStackTrace();
        }


        LOGGER.info(out);

    }


    @Test
    public void testCVC4Splitter() {

        LOGGER.info("Test CVC4");

        String test =  ".*' +[Oo][Rr] +'";

        Ast a = new RegexParser().parse(test);

        LOGGER.info(a.toDot());
        CVC4RegexSplitter splitter = new CVC4RegexSplitter(a);
        String out = splitter.process();
        LOGGER.info(a.toDot());
        LOGGER.info(out);

    }


    @Test
    public void testCVC4Translator1() {

        ConstraintNetwork tm = new ConstraintNetwork();

        Node x = new Operand("x", OperandKind.STRVAR);
        Node or = new Operand(".*' +[Oo][Rr] +'", OperandKind.STRREXP);
        Node v1 = new Operand("sv1", OperandKind.STRVAR);
        Node orv1 = tm.addOperation(OperationKind.CONCAT, or, v1);
        Node eq = new Operand("'.*=.*'", OperandKind.STRREXP);
        Node v2 = new Operand("sv2", OperandKind.STRVAR);
        Node orv1comp = tm.addOperation(OperationKind.CONCAT, eq, v2);
        Node orv1compv2 = tm.addOperation(OperationKind.CONCAT, orv1, orv1comp);

        tm.addConstraint(OperationKind.STR_NEQUALS,v1,v2);
        tm.addConstraint(OperationKind.MATCHES, x, orv1compv2);

        LOGGER.info(tm.toDot());

        SmtTranslator sa = OutputFormat.CVC4.getTranslator();
        try {
            sa.setConstraintNetwork(tm);
        } catch (NotSupportedException e) {
            assert(false);
        }
        String out = "" ;
        try {
            out = sa.translate();

        } catch (NotSupportedException e) {
            e.printStackTrace();
        }

        LOGGER.info(out);
    }

    @Test
    public void testCVC4Translator2() {

        ConstraintNetwork tm2 = new ConstraintNetwork();
        Node x = new Operand("x", OperandKind.STRVAR);
        String sor = ".*' +[Oo][Rr] +'";
        Node or = new Operand(sor, OperandKind.STRREXP);

        Node v1 = new Operand("sv7", OperandKind.NUMVAR);

        Node toStrV1 = tm2.addOperation(OperationKind.TOSTR, v1);

        Node orv1 = tm2.addOperation(OperationKind.CONCAT, or, toStrV1);

        Node eq = new Operand(" +\\>= +", OperandKind.STRREXP);

        Node orv1comp = tm2.addOperation(OperationKind.CONCAT, orv1, eq);

        Node v2 = new Operand("sv8", OperandKind.NUMVAR);

        Node toStrV2 = tm2.addOperation(OperationKind.TOSTR, v2);

        Node orv1compv2 = tm2.addOperation(OperationKind.CONCAT, orv1comp, toStrV2);

        String scomment = "(\\<!\\-\\-|#)";
        Node comment = new Operand(scomment, OperandKind.STRREXP);

        tm2.addOperation(OperationKind.CONCAT,orv1compv2,comment);

        tm2.addConstraint(OperationKind.GREATEREQ, v1,v2);

        tm2.setStartNode(orv1compv2);
        tm2.addConstraint(OperationKind.MATCHES, x, orv1compv2);

        SmtTranslator sa = OutputFormat.CVC4.getTranslator();
        try {
            sa.setConstraintNetwork(tm2);
        } catch (NotSupportedException e) {
            assert(false);
        }
        String out = "" ;
        try {
            out = sa.translate();

        } catch (NotSupportedException e) {
            e.printStackTrace();
        }

        LOGGER.info(out);
    }

    @Test
    public void testCVC4Escape() {
        String s = "SELECT \\* FROM salaries WHERE userid = ";

        String s2 = CVC4Escape.escapeSpecialCharacters(s);

        LOGGER.info(s2);

    }

    @Test
    public void testSmtEscape() {
        String s = "\"SELECT \\* FROM salaries WHERE userid = \"";

        String s2 = SmtEscape.trimQuotes(s);

        LOGGER.info(s2);

    }


    @Test
    public void testZ3Splitter1() {

        LOGGER.info("Test Z3");

        String test =  ".*(\\<((! *- *-)?|( *- *-)?\\>)|\\< *CDATA\\[\\[.*\\]\\] *\\>).";

        RegexParser rp = new RegexParser();
        Ast regex = rp.parse(test);
        //Ast a = RegexParser.getInstance().parse(test);

        LOGGER.info(regex.toDot());

        Z3RegexSplitter splitter = new Z3RegexSplitter(regex);
        splitter.process();
        String out = splitter.getResult();
        LOGGER.info(out);

    }

    @Test
    public void testZ3Splitter2() {
        String xss = "\\< *[Ss] *\\>[a-z]";
        RegexParser rp = new RegexParser();
        Ast regex = rp.parse(xss);
        LOGGER.info(regex.toDot());
        Z3RegexSplitter splitter = new Z3RegexSplitter(regex);
        splitter.process();
        String out = splitter.getResult();
        LOGGER.info(out);

    }
    @Test
    public void testS3Splitter1() {

        LOGGER.info("Test S3");

        String test =  ".*(\\<((! *- *-)?|( *- *-)?\\>)|\\< *CDATA\\[\\[.*\\]\\] *\\>).";

        RegexParser rp = new RegexParser();
        Ast regex = rp.parse(test);
        //Ast a = RegexParser.getInstance().parse(test);

        LOGGER.info(regex.toDot());

        S3RegexSplitter splitter = new S3RegexSplitter(regex);
        String out = splitter.process();
        splitter.getResult();
        LOGGER.info(out);

    }


    private static String script = "\\< *[Ss][Cc][Rr][Ii][Pp][Tt] *\\>" +
            "[a-zA-Z0-9\\(\\);]+\\</ *[Ss][Cc][Rr][Ii][Pp][Tt] \\>";

    private static String img = "\\< *[Ii][Mm][Gg] [Ss][Rr][Cc]=[Jj][Aa][Vv][Aa][Ss][Cc]" +
            "[Rr][Ii][Pp][Tt]:[a-zA-Z0-9\\(\\);]+ *\\>";

    private static String xss = "(" + script + "|" + img + ")";


    @Test
    public void testS3Splitter2() {

        LOGGER.info("Test S3");

        RegexParser rp = new RegexParser();
        Ast regex = rp.parse(xss);
        //Ast a = RegexParser.getInstance().parse(test);

        S3RegexSplitter splitter = new S3RegexSplitter(regex);
        String out = splitter.process();
        splitter.getResult();
        LOGGER.info(out);
        //LOGGER.info(regex.toDot());

    }

    @Test
    public void testApp() {
        LOGGER.info("test app");
        Pattern p = Pattern.compile("[0-9A-Z0-9]{3}\\-[0-9A-Z0-9]{3}\\-([0-9A-Z0-9\\-]+)");

        Matcher m = p.matcher("APP-WIX-51515");

        if(m.matches())
            LOGGER.info(m.group(1));

    }

}


