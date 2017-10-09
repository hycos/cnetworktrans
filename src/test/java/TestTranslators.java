import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import com.github.hycos.cnetwork.core.graph.ConstraintNetworkBuilder;
import com.github.hycos.cnetwork.core.graph.Node;
import com.github.hycos.cnetwork.core.graph.NodeKind;
import com.github.hycos.cnetwork.core.graph.Operand;
import com.github.hycos.cnetwork.exception.EUFInconsistencyException;
import org.snt.cnetworktrans.core.OutputFormat;
import org.snt.cnetworktrans.core.RegexParser;
import org.snt.cnetworktrans.exceptions.NotSupportedException;
import org.snt.cnetworktrans.lang.SmtEscape;
import org.snt.cnetworktrans.lang.SmtTranslator;
import org.snt.cnetworktrans.lang.cvc4.CVC4Escape;
import org.snt.cnetworktrans.lang.cvc4.CVC4RegexSplitter;
import org.snt.cnetworktrans.lang.s3.S3RegexSplitter;
import org.snt.cnetworktrans.lang.z3.Z3RegexSplitter;
import org.snt.inmemantlr.exceptions.ParseTreeProcessorException;
import org.snt.inmemantlr.tree.ParseTree;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class TestTranslators {

    final static Logger LOGGER = LoggerFactory.getLogger(TestTranslators.class);


    private static ConstraintNetworkBuilder cn = null;

    @Before
    public void setUp() throws Exception {
        cn = new ConstraintNetworkBuilder();

        Operand a = new Operand("a", NodeKind.NUMVAR);
        Operand b = new Operand("b", NodeKind.NUMVAR);
        Operand c = new Operand("20", NodeKind.NUMLIT);

        Node add = cn.addOperation(NodeKind.ADD,a,b);
        Node smeq = cn.addConstraint(NodeKind.SMALLEREQ, add, c);


        Operand s = new Operand("s1", NodeKind.STRVAR);
        Operand ip = new Operand("a*", NodeKind.STRREXP);

        Node matches = cn.addConstraint(NodeKind.MATCHES, s, ip);

        Node len = cn.addOperation(NodeKind.LEN,s);

        Node lencon = cn.addConstraint(NodeKind.GREATEREQ, len, c);

        Node conv = cn.addOperation(NodeKind.TOSTR, a);

        Node matches2 = cn.addConstraint(NodeKind.MATCHES, s, conv);
    }


    @Test
    public void testZ3() {


        LOGGER.info("Test Z3");
        SmtTranslator sa = OutputFormat.Z3STR2.getTranslator();
        try {
            sa.setConstraintNetworkBuilder(cn);
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

        ConstraintNetworkBuilder simple = new ConstraintNetworkBuilder();

        Operand a = new Operand("a", NodeKind.STRVAR);
        Operand b = new Operand("b", NodeKind.STRVAR);

        try {
            Node add = simple.addConstraint(NodeKind.NEQUALS,a,b);
        } catch (EUFInconsistencyException e) {
            Assert.assertFalse(true);
        }

        LOGGER.info("Test S3");
        SmtTranslator sa = OutputFormat.S3.getTranslator();
        try {
            sa.setConstraintNetworkBuilder(simple);
        } catch (NotSupportedException e) {
            assert(false);
        }
        String out = null;
        try {
            out = sa.translate();
        } catch (NotSupportedException | ParseTreeProcessorException e) {
            Assert.assertFalse(true);
        }


        LOGGER.info(out);

    }

    @Test
    public void testCVC4() {

        LOGGER.info("Test CVC4");
        SmtTranslator sa = OutputFormat.CVC4.getTranslator();
        try {
            sa.setConstraintNetworkBuilder(cn);
        } catch (NotSupportedException e) {
            e.printStackTrace();
        }
        String out = null;
        try {
            out = sa.translate();
        } catch (NotSupportedException | ParseTreeProcessorException e) {
            Assert.assertFalse(true);
        }



        LOGGER.info(out);

    }


    @Test
    public void testCVC4Splitter() {

        LOGGER.info("Test CVC4");

        String test =  ".*' +[Oo][Rr] +'";

        ParseTree a = new RegexParser().parse(test);

        LOGGER.info(a.toDot());
        CVC4RegexSplitter splitter = new CVC4RegexSplitter(a);
        String out = null;
        try {
            out = splitter.process();
        } catch (ParseTreeProcessorException e) {
            Assert.assertFalse(true);
        }
        LOGGER.info(a.toDot());
        LOGGER.info(out);

    }


    @Test
    public void testCVC4Translator1() {

        try {
            ConstraintNetworkBuilder tm = new ConstraintNetworkBuilder();

            Node x = new Operand("x", NodeKind.STRVAR);
            Node or = new Operand(".*' +[Oo][Rr] +'", NodeKind.STRREXP);
            Node v1 = new Operand("sv1", NodeKind.STRVAR);
            Node orv1 = tm.addOperation(NodeKind.CONCAT, or, v1);
            Node eq = new Operand("'.*=.*'", NodeKind.STRREXP);
            Node v2 = new Operand("sv2", NodeKind.STRVAR);
            Node orv1comp = tm.addOperation(NodeKind.CONCAT, eq, v2);
            Node orv1compv2 = tm.addOperation(NodeKind.CONCAT, orv1, orv1comp);

            try {
                tm.addConstraint(NodeKind.STR_NEQUALS, v1, v2);
            } catch (EUFInconsistencyException e) {
                Assert.assertFalse(true);
            }
            try {
                tm.addConstraint(NodeKind.MATCHES, x, orv1compv2);
            } catch (EUFInconsistencyException e) {
                Assert.assertFalse(true);
            }

            //LOGGER.info(tm.toDot());

            SmtTranslator sa = OutputFormat.CVC4.getTranslator();
            try {
                sa.setConstraintNetworkBuilder(tm);
            } catch (NotSupportedException e) {
                assert (false);
            }
            String out = "";
            try {
                out = sa.translate();
            } catch (NotSupportedException | ParseTreeProcessorException e) {
                Assert.assertFalse(true);
            }
        } catch (EUFInconsistencyException e) {
            Assert.assertFalse(true);
        }

        //LOGGER.info(out);
    }

    @Test
    public void testCVC4Translator2() {

        try {
            ConstraintNetworkBuilder tm2 = new ConstraintNetworkBuilder();

            Node x = new Operand("x", NodeKind.STRVAR);
            String sor = ".*' +[Oo][Rr] +'";
            Node or = new Operand(sor, NodeKind.STRREXP);

            Node v1 = new Operand("sv7", NodeKind.NUMVAR);

            Node toStrV1 = tm2.addOperation(NodeKind.TOSTR, v1);

            Node orv1 = tm2.addOperation(NodeKind.CONCAT, or, toStrV1);

            Node eq = new Operand(" +\\>= +", NodeKind.STRREXP);

            Node orv1comp = tm2.addOperation(NodeKind.CONCAT, orv1, eq);

            Node v2 = new Operand("sv8", NodeKind.NUMVAR);

            Node toStrV2 = tm2.addOperation(NodeKind.TOSTR, v2);

            Node orv1compv2 = tm2.addOperation(NodeKind.CONCAT, orv1comp, toStrV2);

            String scomment = "(\\<!\\-\\-|#)";
            Node comment = new Operand(scomment, NodeKind.STRREXP);

            tm2.addOperation(NodeKind.CONCAT, orv1compv2, comment);

            tm2.addConstraint(NodeKind.GREATEREQ, v1, v2);

            tm2.setStartNode(orv1compv2);
            tm2.addConstraint(NodeKind.MATCHES, x, orv1compv2);

            SmtTranslator sa = OutputFormat.CVC4.getTranslator();
            try {
                sa.setConstraintNetworkBuilder(tm2);
            } catch (NotSupportedException e) {
                assert (false);
            }
            String out = "";
            try {
                out = sa.translate();
            } catch (NotSupportedException | ParseTreeProcessorException e) {
                Assert.assertFalse(true);
            }
        } catch(EUFInconsistencyException e) {
            Assert.assertFalse(true);
        }


        //LOGGER.info(out);
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
        ParseTree regex = rp.parse(test);
        //ParseTree a = RegexParser.getInstance().parse(test);

        LOGGER.info(regex.toDot());

        Z3RegexSplitter splitter = new Z3RegexSplitter(regex);
        try {
            splitter.process();
        } catch (ParseTreeProcessorException e) {
            Assert.assertFalse(true);
        }
        String out = splitter.getResult();
        LOGGER.info(out);

    }

    @Test
    public void testZ3Splitter2() {
        String xss = "\\< *[Ss] *\\>[a-z]";
        RegexParser rp = new RegexParser();
        ParseTree regex = rp.parse(xss);
        LOGGER.info(regex.toDot());
        Z3RegexSplitter splitter = new Z3RegexSplitter(regex);
        try {
            splitter.process();
        } catch (ParseTreeProcessorException e) {
            Assert.assertFalse(true);
        }
        String out = splitter.getResult();
        LOGGER.info(out);

    }
    @Test
    public void testS3Splitter1() {

        LOGGER.info("Test S3");

        String test =  ".*(\\<((! *- *-)?|( *- *-)?\\>)|\\< *CDATA\\[\\[.*\\]\\] *\\>).";

        RegexParser rp = new RegexParser();
        ParseTree regex = rp.parse(test);
        //ParseTree a = RegexParser.getInstance().parse(test);

        LOGGER.info(regex.toDot());

        S3RegexSplitter splitter = new S3RegexSplitter(regex);
        String out = null;
        try {
            out = splitter.process();
        } catch (ParseTreeProcessorException e) {
            Assert.assertFalse(true);
        }
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
        ParseTree regex = rp.parse(xss);
        //ParseTree a = RegexParser.getInstance().parse(test);

        S3RegexSplitter splitter = new S3RegexSplitter(regex);
        String out = null;
        try {
            out = splitter.process();
        } catch (ParseTreeProcessorException e) {
            Assert.assertFalse(true);
        }
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


