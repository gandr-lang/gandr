INSERT INTO purpose VALUES('surface-features','Area','struct','An area of the ledger, a row''s `area`.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('surface-features','Feature','struct','One row of the ledger.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('surface-features','FeatureId','struct','A feature''s identifier, its row''s `id`.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('surface-features','FeatureLedger','struct','The features ledger: every row, in the dump''s order, which is by `id`.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('surface-features','FeaturesFault','enum','Why the features ledger could not be read or could not answer.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('surface-features','Malformed','enum','How a line of the dump fails to be what the reader reads.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('surface-features','ShownFeature','struct','A feature as `ledger show` prints it: its row, its exemplars'' sources and its corpus witnesses'' paths.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('surface-features','Status','enum','Where a feature stands.',NULL,'fits','sound',NULL);
