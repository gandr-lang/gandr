INSERT INTO purpose VALUES('workflow-github','Body','struct','The text a `gh` invocation reads as a body on standard input.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-github','Feed','enum','What a `gh` invocation reads on standard input: nothing, or a body.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-github','Invocation','struct','A command as a shell spells it, the name a refusal gives what it refused.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-github','READ_PAUSE','constant','The pause a read takes after a server error before it runs the invocation again.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-github','Site','struct','One call site of `gh`: the scope that holds the call and its verb, declared on the one line that the check of the API budget reads.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-github','Word','struct','One word of a declared site of `gh`, whose text comes from the declared line alone.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-github','error::GitHubError','enum','Why a `gh` invocation gave no answer its caller reads: it did not start, exited unsuccessfully, or answered what the caller does not parse.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-github','read','function','Runs a read-only `gh` invocation, again after a pause while GitHub answers it with a server error, for at most three attempts.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('workflow-github','run','function','Runs a `gh` invocation, feeding it a body when asked, and returns its standard output or the refusal naming it.',NULL,'fits','sound',NULL);
