# HX LAB v0.8.4 CAT Preview

## v0.8.4
- Added Kenwood TS-2000 as a selectable CAT radio model.
- Added TS-2000 live frequency, operating-mode, and PTT-state polling.
- Added TS-2000 CAT PTT using native `TX;` and `RX;` commands.
- Preserved Yaesu FT-710 commands and behavior unchanged.
- Added 57600 baud to the CAT baud-rate choices.
- Saved model selection and delayed CAT auto-connect continue to apply.

# HX LAB v0.8.3 CAT Preview

## v0.8.3
- Added a one-shot CAT auto-connect attempt two seconds after HX opens.
- Auto-connect runs only when CAT is enabled and a saved COM port is available.
- A powered-off or unavailable radio does not interrupt startup with a popup.
- Manual CAT Connect remains available after an unsuccessful startup attempt.

# HX LAB v0.8.2 CAT Preview

## v0.8.2
- CAT is enabled automatically at startup when a saved COM-port profile exists.
- Expected serial errors caused by powering off or unplugging the radio are now kept out of Normal debug.
- CAT transport and PTT-release details remain available in Developer debug.

# HX LAB v0.8.1 CAT Preview

## v0.8.1

- Fixed the 1 kHz tune function so it uses the selected optional PTT method.
- CAT, RTS, and DTR PTT are asserted before tune audio begins.
- PTT is released when the tune tone stops or if tone startup fails.
- CAT-disabled and VOX behavior remain unchanged.

# HX LAB v0.7.5

## v0.7.5

- Return immediately to Listening after an unrecoverable header or payload CRC failure.
- Clear the locked candidate and HX busy state without waiting for audio silence.
- Added a 600 ms CRC-recovery cooldown to prevent immediate relock on the same continuous SSB/audio segment.
- Keep the CRC ERROR indicator visible for operator feedback.

# HX LAB v0.7.4

- Fixed the transmit progress bar so the Idle/status text remains centered across the full resized bar.
- The progress bar redraws whenever its canvas geometry changes.

# HX LAB Changelog

## v0.7.4

- Fixed Station / QSO Information TX SNR synchronization during automatic file-transfer metadata exchange.
- SNR bundled in FILE_OFFER and FILE_ACCEPT now updates the same TX SNR field used by normal SNR reports.
- FILE_ACK peer-reported SNR updates remain supported.
- RX SNR measurement behavior, file-transfer framing, HX-F, and HX-N are unchanged.

## v0.7.2

- Disabled the transmit message editor, SEND button, service-tag selector, profile requests, and SNR requests during both incoming and outgoing file transfers.
- The message editor temporarily displays: `Text messages disabled during file transfer. Please wait.` and restores the prior draft after the transfer completes, fails, is rejected, or is cancelled.
- CANCEL FILE remains available throughout an active transfer.
- FILE_OFFER and FILE_ACCEPT now both include the local operator profile and the best available SNR measurement for the peer before the first file chunk.
- Removed post-transfer `POST_DRAIN_DONE` / `POST_DRAIN_ACK` RF traffic. No internal post-drain messages are shown to operators.
- Changed the TX/file progress bar from blue to purple.
- Reduced DECODER OUTPUT panel height.
- Removed the unrequested application subtitle.
- HX-F, HX-N, file chunk framing, and spectrum behavior are unchanged.

## v0.8.0 CAT Preview

- Added an optional CAT/PTT Manager; CAT is disabled by default.
- Added FT-710 CAT support for live VFO-A frequency, operating mode, and PTT-state polling.
- Added CAT connection indicator and radio-mode display.
- Replaced the frequency placeholder with live CAT frequency while connected.
- Added PTT methods: VOX, CAT (`TX1;` / `TX0;`), RTS, and DTR.
- Added COM-port discovery, baud-rate selection, connect/disconnect controls, and persisted settings.
- Added `pyserial` dependency.
- Preserved the existing HX modem, protocol, session, and file-transfer implementation unchanged.
