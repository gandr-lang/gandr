CREATE TABLE requires(
  feature TEXT NOT NULL REFERENCES feature(id),
  needs   TEXT NOT NULL REFERENCES feature(id),
  PRIMARY KEY(feature, needs),
  CHECK(needs <> feature)
) WITHOUT ROWID;
