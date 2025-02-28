package de.tlc4b.tlc;

import de.tlc4b.TLC4BGlobals;
import tlc2.output.Message;

import java.util.*;

public abstract class TLCMessageListener extends Thread {
	private volatile boolean tlcRunning = true;
	private final List<Message> messages = new ArrayList<>();
	private int lastMessageIndex = 0;

	@Override
	public void run() {
		while (tlcRunning) {
			List<Message> currentMessages = TLC4BGlobals.getCurrentMessages();
			int currentMessageIndex = currentMessages.size();
			if (lastMessageIndex < currentMessageIndex) {
				for (int i = lastMessageIndex; i < currentMessageIndex; i++) {
					messages.add(currentMessages.get(i));
					onMessage(currentMessages.get(i));
				}
				lastMessageIndex = currentMessageIndex;
			}
		}
	}

	public void finish() {
		tlcRunning = false;
		this.interrupt();
	}

	public abstract void onMessage(Message message);

	public List<Message> getMessages() {
		return messages;
	}
}
