package de.tlc4b;

import java.io.BufferedWriter;
import java.io.Closeable;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.Date;
import java.util.Locale;
import java.util.StringJoiner;

import tlc2.output.Message;

@FunctionalInterface
public interface TLCMessageHandler extends Closeable {

	void onMessage(Message msg);

	default void close() {
		// NO-OP
	}

	static TLCMessageHandler printToStream(OutputStream out) throws IOException {
		PrintWriter w = new PrintWriter(new BufferedWriter(new OutputStreamWriter(out, StandardCharsets.UTF_8)), true);
		return new TLCMessageHandler() {
			@Override
			public void onMessage(Message msg) {
				long epochMillis = msg.getDate() != null ? msg.getDate().getTime() : 0;
				String[] params = msg.getParameters() != null ? msg.getParameters() : new String[0];
				StringJoiner j = new StringJoiner("|");
				for (String p : params) {
					j.add(p.replace("\n", " ").replace("|", ";"));
				}
				w.println(String.format(Locale.ROOT, "%d|%d|%d|%s", msg.getMessageClass(), msg.getMessageCode(), epochMillis, j));
			}

			@Override
			public void close() {
				w.close();
			}
		};
	}

	static Message fromLine(String line) {
		String[] split = line.split("\\|", 4);
		int msgClass = Integer.parseInt(split[0]);
		int msgCode = Integer.parseInt(split[1]);
		Date msgDate = new Date(Long.parseLong(split[2]));
		String[] msgParams = split[3].split("\\|");
		return new Message(msgClass, msgCode, msgParams, msgDate);
	}
}
