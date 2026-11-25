INSERT INTO purpose VALUES('workflow-debt-ledger','Header','struct','The lines a ledger is written under, each without its `# `.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-debt-ledger','Ledger','struct','The keys a ledger holds: the debt a check has committed to owe.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-debt-ledger','Standing','enum','Whether a check''s findings and its ledger agree, from which the check chooses its exit.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-debt-ledger','Text','struct','A ledger''s text, as read from its file or written to it.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-debt-ledger','Verdict','struct','What a check''s findings owe against its ledger: the new findings and the stale keys.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-debt-ledger','error::LedgerError','enum','Why a ledger''s text does not read: a line no key reads from.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-debt-ledger','write','function','The text that regenerates a ledger: the header as `#` lines, then each distinct key once, in order.',NULL,'fits','sound',NULL);
