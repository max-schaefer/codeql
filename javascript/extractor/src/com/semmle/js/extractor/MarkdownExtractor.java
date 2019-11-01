package com.semmle.js.extractor;

import java.io.IOException;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.semmle.jcorn.Locutil;
import com.semmle.js.ast.Position;
import com.semmle.js.extractor.ExtractorConfig.SourceType;
import com.semmle.js.parser.ParseError;
import com.semmle.util.trap.TrapWriter;

public class MarkdownExtractor implements IExtractor {
  private static Pattern JS_CODEBLOCK =
      Pattern.compile("(?is)(?:^|\n)```(?:javascript|js)[^\n]*\n(.*?)(?<=\n)```");

  private ExtractorConfig config;

  public MarkdownExtractor(ExtractorConfig config) {
    this.config = config;
  }

  @Override
  public LoCInfo extract(TextualExtractor textualExtractor) throws IOException {
    LoCInfo result = new LoCInfo(0, 0);

    String src = textualExtractor.getSource();
    ScopeManager scopeManager =
        new ScopeManager(textualExtractor.getTrapwriter(), config.getEcmaVersion());

    // extract all JavaScript code blocks
    Matcher m = JS_CODEBLOCK.matcher(src);
    while (m.find()) {
      LoCInfo snippetLoC = null;
      String source = m.group(1);
      if (source != null && !source.trim().isEmpty()) {
        Position startPos = Locutil.getLineInfo(src, m.start());
        snippetLoC =
            extractSnippet(
                1,
                config.withSourceType(SourceType.AUTO),
                scopeManager,
                textualExtractor,
                source,
                startPos.getLine()+2,
                1);
        result.add(snippetLoC);
      }
    }

    return result;
  }

  private LoCInfo extractSnippet(
      int toplevelKind,
      ExtractorConfig config,
      ScopeManager scopeManager,
      TextualExtractor textualExtractor,
      String source,
      int line,
      int column) {
    TrapWriter trapwriter = textualExtractor.getTrapwriter();
    LocationManager locationManager = textualExtractor.getLocationManager();
    LocationManager scriptLocationManager =
        new LocationManager(
            locationManager.getSourceFile(), trapwriter, locationManager.getFileLabel());
    scriptLocationManager.setStart(line, column);
    JSExtractor extractor = new JSExtractor(config);
    try {
      TextualExtractor tx =
          new TextualExtractor(
              trapwriter,
              scriptLocationManager,
              source,
              config.getExtractLines(),
              textualExtractor.getMetrics());
      return extractor.extract(tx, source, toplevelKind, scopeManager).snd();
    } catch (ParseError e) {
      e.setPosition(scriptLocationManager.translatePosition(e.getPosition()));
      throw e.asUserError();
    }
  }
}
