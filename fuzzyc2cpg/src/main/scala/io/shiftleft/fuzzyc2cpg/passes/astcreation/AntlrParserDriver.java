package io.shiftleft.fuzzyc2cpg.passes.astcreation;

import static org.antlr.v4.runtime.Token.EOF;

import io.shiftleft.codepropertygraph.generated.EdgeTypes;
import io.shiftleft.codepropertygraph.generated.nodes.NewComment;
import io.shiftleft.codepropertygraph.generated.nodes.NewFile;
import io.shiftleft.fuzzyc2cpg.ast.AstNode;
import io.shiftleft.fuzzyc2cpg.ast.AstNodeBuilder;
import io.shiftleft.fuzzyc2cpg.ast.logical.statements.CompoundStatement;
import io.shiftleft.fuzzyc2cpg.parser.AntlrParserDriverObserver;
import io.shiftleft.fuzzyc2cpg.parser.CommonParserContext;
import io.shiftleft.fuzzyc2cpg.parser.TokenSubStream;
import io.shiftleft.passes.DiffGraph;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;
import java.util.function.Consumer;
import jdk.nashorn.internal.runtime.ParserException;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.DefaultErrorStrategy;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenSource;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeListener;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import org.antlr.v4.runtime.tree.TerminalNodeImpl;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.antlr.v4.runtime.tree.pattern.TokenTagToken;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.ErrorNode;
import scala.Some;
import scala.collection.immutable.List$;

abstract public class AntlrParserDriver {
    // TODO: This class does two things:
    // * It is a driver for the ANTLRParser, i.e., the parser
    // that creates ParseTrees from Strings. It can also already
    // 'walk' the ParseTree to create ASTs.
    // * It is an AST provider in that it will notify watchers
    // when ASTs are ready.
    // We should split this into two classes.

    public Stack<AstNodeBuilder<? extends AstNode>> builderStack = new Stack<>();
    public TokenSubStream stream;
    public String filename;

    private ParseTreeListener listener;
    private CommonParserContext context = null;
    public DiffGraph.Builder cpg;
    private final List<AntlrParserDriverObserver> observers = new ArrayList<>();
    private NewFile fileNode;
    private Parser antlrParser;

    public AntlrParserDriver() {
        super();
    }

    public void setFileNode(NewFile fileNode) {
        this.fileNode = fileNode;
    }

    public abstract ParseTree parseTokenStreamImpl(TokenSubStream tokens);

    public abstract Lexer createLexer(CharStream input);

    public DiffGraph.Builder parseAndWalkFile(String filename, DiffGraph.Builder diffGraph) throws ParserException {
        cpg  = diffGraph;
        handleHiddenTokens(filename);
        TokenSubStream stream = createTokenStreamFromFile(filename);
		for(int i = 1; i <= stream.getNumberOfOnChannelTokens(); i++) {
			System.out.println(stream.LT(i).getText());
		}
		
        initializeContextWithFile(filename, stream);

        ParseTree tree = parseTokenStream(stream);
        walkTree(tree);
        return cpg;
    }

    private void handleHiddenTokens(String filename) {
        CommonTokenStream tokenStream = createStreamOfHiddenTokensFromFile(filename);
        TokenSource tokenSource = tokenStream.getTokenSource();

        while (true){
            Token token = tokenSource.nextToken();
            if (token.getType() == EOF) {
                break;
            }
            if (token.getChannel() != Token.HIDDEN_CHANNEL) {
                continue;
            }
            int line = token.getLine();
            String text = token.getText();
            NewComment commentNode = new NewComment(
                    new Some<>(line),
                    text
            );
            cpg.addNode(commentNode);
            cpg.addEdge(fileNode, commentNode, EdgeTypes.AST, List$.MODULE$.empty());
        }
    }

    public void parseAndWalkTokenStream(TokenSubStream tokens)
            throws ParserException {
        filename = "";
        stream = tokens;
        ParseTree tree = parseTokenStream(tokens);
        walkTree(tree);
    }


    public ParseTree parseAndWalkString(String input) throws ParserException {
        ParseTree tree = parseString(input);
        walkTree(tree);
        return tree;
    }

    public CompoundStatement getResult() {
        return (CompoundStatement) builderStack.peek().getItem();
    }

    public ParseTree parseString(String input) throws ParserException {
        CharStream inputStream = CharStreams.fromString(input);
        Lexer lex = createLexer(inputStream);
        TokenSubStream tokens = new TokenSubStream(lex);
        ParseTree tree = parseTokenStream(tokens);
        return tree;
    }

    public ParseTree parseTokenStream(TokenSubStream tokens)
            throws ParserException {
        ParseTree returnTree = parseTokenStreamImpl(tokens);
        if (returnTree == null) {
            throw new ParserException("");
        }
        return returnTree;
    }

    public void setAntlrParser(Parser parser) {
        antlrParser = parser;
    }

    public Parser getAntlrParser() {
        return antlrParser;
    }

    protected TokenSubStream createTokenStreamFromFile(String filename)
            throws ParserException {

        CharStream input = createInputStreamForFile(filename);
        Lexer lexer = createLexer(input);
        TokenSubStream tokens = new TokenSubStream(lexer); // MARK
        return tokens;

    }

    private CharStream createInputStreamForFile(String filename) {

        try {
			System.out.println("reading file in createInputStreamForFile: " + filename);
            return CharStreams.fromFileName(filename);
        } catch (IOException exception) {
            throw new RuntimeException(String.format("Unable to find source file [%s]", filename));
        }

    }

    protected CommonTokenStream createStreamOfHiddenTokensFromFile(String filename) {
        CharStream input = createInputStreamForFile(filename);
        Lexer lexer = createLexer(input);
        return new CommonTokenStream(lexer, Token.HIDDEN_CHANNEL);
    }

    protected void walkTree(ParseTree tree) {
		System.out.println("Class of tree: " + tree.getClass().getName());
		System.out.println("Class of listener: " + getListener().getClass().getName());
        ParseTreeWalker walker = new ParseTreeWalker();
		// MARK: Einstiegspunkt
		/*
		ParserRuleContext ctx0 = new ParserRuleContext();
		ParserRuleContext ctx1 = new ParserRuleContext(ctx0, 1);
		TokenTagToken ttt = new TokenTagToken("Call", 27, "Call");
		TerminalNode tn = new TerminalNodeImpl(ttt);
		ctx1.addChild(tn);
		ctx0.addChild(ctx1);
		listener.enterEveryRule(ctx0);
		listener.exitEveryRule(ctx0);
		*/
		//System.out.println("!!!!!!!!!!!!!! calling walk !!!!!!!!!!!!!!");
        walk(getListener(), tree);
		//System.out.println("!!!!!!!!!!!!!! called walk !!!!!!!!!!!!!!");
    }

	/**
	 * Performs a walk on the given parse tree starting at the root and going down recursively
	 * with depth-first search. On each node, {@link ParseTreeWalker#enterRule} is called before
	 * recursively walking down into child nodes, then
	 * {@link ParseTreeWalker#exitRule} is called after the recursive call to wind up.
	 * @param listener The listener used by the walker to process grammar rules
	 * @param t The parse tree to be walked on
	 */
	// Adapted from: https://github.com/antlr/antlr4/blob/master/runtime/Java/src/org/antlr/v4/runtime/tree/ParseTreeWalker.java
	public void walk(ParseTreeListener listener, ParseTree tree) {
		if (tree instanceof ErrorNode) {
			listener.visitErrorNode((ErrorNode) tree);
			return;
		}
		else if (tree instanceof TerminalNode) {
			listener.visitTerminal((TerminalNode) tree);
			return;
		}
		RuleNode ruleNode = (RuleNode) tree;
        enterRule(listener, ruleNode);
        int n = ruleNode.getChildCount();
        for (int i = 0; i<n; i++) {
            walk(listener, ruleNode.getChild(i));
        }
		exitRule(listener, ruleNode);
    }

	/**
	 * Enters a grammar rule by first triggering the generic event {@link ParseTreeListener#enterEveryRule}
	 * then by triggering the event specific to the given parse tree node
	 * @param listener The listener responding to the trigger events
	 * @param r The grammar rule containing the rule context
	 */
	// Adapted from: https://github.com/antlr/antlr4/blob/master/runtime/Java/src/org/antlr/v4/runtime/tree/ParseTreeWalker.java
    protected void enterRule(ParseTreeListener listener, RuleNode ruleNode) {
		ParserRuleContext ctx = (ParserRuleContext) ruleNode.getRuleContext();
		//System.out.println("ParserRuleContext:");
		//System.out.println(ctx);
		listener.enterEveryRule(ctx);
		ctx.enterRule(listener);
    }


	/**
	 * Exits a grammar rule by first triggering the event specific to the given parse tree node
	 * then by triggering the generic event {@link ParseTreeListener#exitEveryRule}
	 * @param listener The listener responding to the trigger events
	 * @param r The grammar rule containing the rule context
	 */
	// Adapted from: https://github.com/antlr/antlr4/blob/master/runtime/Java/src/org/antlr/v4/runtime/tree/ParseTreeWalker.java
	protected void exitRule(ParseTreeListener listener, RuleNode ruleNode) {
		ParserRuleContext ctx = (ParserRuleContext) ruleNode.getRuleContext();
		ctx.exitRule(listener);
		listener.exitEveryRule(ctx);
    }

    protected void initializeContextWithFile(String filename,
                                             TokenSubStream stream) {
        setContext(new CommonParserContext());
        getContext().filename = filename;
        getContext().stream = stream;
        initializeContext(getContext());
    }

    protected boolean isRecognitionException(RuntimeException ex) {

        return ex.getClass() == ParseCancellationException.class
                && ex.getCause() instanceof RecognitionException;
    }

    protected void setLLStarMode(Parser parser) {
        parser.removeErrorListeners();
        parser.setErrorHandler(new DefaultErrorStrategy());
    }

    protected void setSLLMode(Parser parser) {
        parser.removeErrorListeners();
        parser.setErrorHandler(new BailErrorStrategy());
    }

    public void initializeContext(CommonParserContext context) {
        filename = context.filename;
        stream = context.stream;
    }

    public void setStack(Stack<AstNodeBuilder<? extends AstNode>> aStack) {
        builderStack = aStack;
    }

    // //////////////////

    public void addObserver(AntlrParserDriverObserver observer) {
        observers.add(observer);
    }

    private void notifyObservers(Consumer<AntlrParserDriverObserver> function) {
        for (AntlrParserDriverObserver observer : observers) {
            function.accept(observer);
        }

    }

    public void begin() {
        notifyObserversOfBegin();
    }

    public void end() {
        notifyObserversOfEnd();
    }

    private void notifyObserversOfBegin() {
        notifyObservers(AntlrParserDriverObserver::begin);
    }

    private void notifyObserversOfEnd() {
        notifyObservers(AntlrParserDriverObserver::end);
    }

    public void notifyObserversOfUnitStart(ParserRuleContext ctx) {
        notifyObservers(observer -> observer.startOfUnit(ctx, filename));
    }

    public void notifyObserversOfUnitEnd(ParserRuleContext ctx) {
        notifyObservers(observer -> observer.endOfUnit(ctx, filename));
    }

    public void notifyObserversOfItem(AstNode aItem) {
        notifyObservers(observer -> observer.processItem(aItem, builderStack));
    }

    public ParseTreeListener getListener() {
        return listener;
    }

    public void setListener(ParseTreeListener listener) {
        this.listener = listener;
    }

    public CommonParserContext getContext() {
        return context;
    }

    public void setContext(CommonParserContext context) {
        this.context = context;
    }

}

