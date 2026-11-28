PRAGMA foreign_keys=OFF;
BEGIN TRANSACTION;
CREATE TABLE reference(
  -- A site's citation of a source. The tree holds no row of this table: the
  -- citations of the crates' documentation make its rows, and `mise run
  -- ledger:references` writes them.
  --
  -- The source cited: the library's citation key, `vault:` and a vault page's
  -- `mint:` uuid, or, for a citation not yet written as a key line, its
  -- locator, `doi:<doi>` in lower case or `arXiv:<identifier>`.
  key         TEXT NOT NULL CONSTRAINT "key is one word" CHECK(key <> '' AND instr(key, ' ') = 0 AND instr(key, char(9)) = 0),
  -- The crate's directory under crates/.
  crate       TEXT NOT NULL CONSTRAINT "crate is a directory under crates/" CHECK(crate GLOB '[a-z]*-[a-z]*' AND crate NOT GLOB '*[^a-z0-9-]*'),
  -- The module whose documentation cites the key: its path, empty for the
  -- crate root, whose documentation is its root source's and its README's.
  module      TEXT NOT NULL CONSTRAINT "module is segments joined by ::, empty for the crate root" CHECK(module NOT GLOB '*[^a-z0-9_:]*'),
  -- What the site takes from the source, as its key line states (#4532):
  --   newest      the newest work stating the construction the site builds;
  --   dependency  a definition, theorem, proof or appendix the site
  --               implements, its key line naming the section with `§`;
  --   anchor      the central statement a narrower newest work specialises;
  --   exemplar    a work before the citation window that no newer work
  --               states;
  -- and, at a site no `fidelity` row records yet:
  --   lineage     the work the site's construction descends from;
  --   background  context the site reads against; every locator's.
  role        TEXT NOT NULL CONSTRAINT "role is newest, dependency, anchor, exemplar, lineage or background" CHECK(role IN ('newest', 'dependency', 'anchor', 'exemplar', 'lineage', 'background')),
  -- The last reading of the source against the site, from its `reading`
  -- row. NULL until the site is read.
  read_commit TEXT CONSTRAINT "read_commit is a full commit id" CHECK(length(read_commit) = 40 AND read_commit NOT GLOB '*[^0-9a-f]*'),
  read_date   TEXT CONSTRAINT "read_date is YYYY-MM-DD" CHECK(read_date GLOB '[0-9][0-9][0-9][0-9]-[0-1][0-9]-[0-3][0-9]'),
  read_blob   TEXT CONSTRAINT "read_blob is a full blob id" CHECK(length(read_blob) = 40 AND read_blob NOT GLOB '*[^0-9a-f]*'),
  PRIMARY KEY(key, crate, module),
  CONSTRAINT "a reading has its commit, its day and its blob, or none of them" CHECK((read_commit IS NULL) = (read_date IS NULL) AND (read_date IS NULL) = (read_blob IS NULL))
) WITHOUT ROWID;
CREATE TABLE work(
  -- A work the crates or the corpus cite, by the key the citations write: the
  -- library's citation key, or its locator, `doi:<doi>` in lower case or
  -- `arXiv:<identifier>`.
  key   TEXT PRIMARY KEY CONSTRAINT "key is a citation key or a locator" CHECK(key <> '' AND instr(key, ' ') = 0 AND instr(key, char(9)) = 0 AND key NOT GLOB 'vault:*'),
  -- The year the work appeared, as its bibliographic record has it. The
  -- citation window reads it before the year a citation key or an arXiv
  -- identifier carries, so a preprint published later takes its published
  -- year. A work cited by a DOI has a row, since a DOI carries no year.
  year  INTEGER NOT NULL CONSTRAINT "year is a year" CHECK(year BETWEEN 1800 AND 2100),
  -- The newest work by the same authors on the same subject, by its locator,
  -- which the window names beside a citation it refuses; NULL when none is
  -- known.
  newer TEXT CONSTRAINT "newer is a locator" CHECK(newer IS NULL OR newer GLOB 'doi:10.*' OR newer GLOB 'arXiv:*')
) WITHOUT ROWID;
INSERT INTO work VALUES('Bauer-efficient_computation_dedekind_reals',2008,NULL);
INSERT INTO work VALUES('Cockx-2018-elaborating_dependent_copattern_matching',2018,'doi:10.1017/s0956796819000182');
INSERT INTO work VALUES('Gavazzo-2022-quantitative_metric_rewriting_abstract_nonexpansive_graded_systems',2022,'doi:10.1145/3571256');
INSERT INTO work VALUES('Plotkin-2013-handling_algebraic_effects',2013,'doi:10.1017/s0956796816000320');
INSERT INTO work VALUES('arXiv:0907.4553',2013,NULL);
INSERT INTO work VALUES('arXiv:1603.01455',2017,'doi:10.1109/lics65433.2025.00012');
INSERT INTO work VALUES('arXiv:1612.09225',2026,NULL);
INSERT INTO work VALUES('arXiv:2001.11001',2021,NULL);
INSERT INTO work VALUES('arXiv:2102.06275',2025,NULL);
INSERT INTO work VALUES('arXiv:2104.14686',2022,'doi:10.1007/978-3-031-94706-3_2');
INSERT INTO work VALUES('arXiv:2109.06049',2022,NULL);
INSERT INTO work VALUES('arXiv:2307.13519',2024,NULL);
INSERT INTO work VALUES('arXiv:2411.11469',2026,NULL);
INSERT INTO work VALUES('arXiv:2510.23517',2026,NULL);
INSERT INTO work VALUES('doi:10.1007/3-540-15975-4_48',1985,NULL);
INSERT INTO work VALUES('doi:10.1007/3-540-17906-2_30',1987,NULL);
INSERT INTO work VALUES('doi:10.1007/3-540-45749-6_17',2002,NULL);
INSERT INTO work VALUES('doi:10.1007/3-540-45842-5_13',2002,NULL);
INSERT INTO work VALUES('doi:10.1007/3-540-45931-6_24',2002,NULL);
INSERT INTO work VALUES('doi:10.1007/3-540-48184-2_32',1988,NULL);
INSERT INTO work VALUES('doi:10.1007/3-540-48959-2_11',1999,'doi:10.2307/2586554');
INSERT INTO work VALUES('doi:10.1007/3-540-48959-2_17',1999,'doi:10.1145/3537668.3537670');
INSERT INTO work VALUES('doi:10.1007/3-540-52335-9_47',1990,NULL);
INSERT INTO work VALUES('doi:10.1007/3-540-61780-9_66',1996,NULL);
INSERT INTO work VALUES('doi:10.1007/978-3-031-57267-8_13',2024,NULL);
INSERT INTO work VALUES('doi:10.1007/978-3-031-63501-4_12',2024,NULL);
INSERT INTO work VALUES('doi:10.1007/978-3-319-20547-2',2015,'doi:10.1112/jlms.12528');
INSERT INTO work VALUES('doi:10.1007/978-3-319-89366-2_16',2018,'doi:10.1145/3290315');
INSERT INTO work VALUES('doi:10.1007/978-3-540-78663-4_9',2008,NULL);
INSERT INTO work VALUES('doi:10.1007/978-3-642-15205-4_26',2010,NULL);
INSERT INTO work VALUES('doi:10.1007/978-3-642-15375-4_16',2010,'doi:10.1017/s0960129514000218');
INSERT INTO work VALUES('doi:10.1007/978-3-642-21691-6_5',2011,NULL);
INSERT INTO work VALUES('doi:10.1007/978-3-642-24452-0_5',2011,NULL);
INSERT INTO work VALUES('doi:10.1007/978-3-642-25379-9_26',2011,NULL);
INSERT INTO work VALUES('doi:10.1007/978-3-642-87374-4_1',1987,NULL);
INSERT INTO work VALUES('doi:10.1007/978-3-662-46678-0_1',2015,'doi:10.1145/3539656');
INSERT INTO work VALUES('doi:10.1007/978-94-007-0954-6',2003,'doi:10.1145/3537668.3537670');
INSERT INTO work VALUES('doi:10.1007/bf01211308',1994,NULL);
INSERT INTO work VALUES('doi:10.1007/bf02020961',1967,NULL);
INSERT INTO work VALUES('doi:10.1007/bfb0053567',1998,'doi:10.1145/2220365.2220367');
INSERT INTO work VALUES('doi:10.1007/bfb0055070',1998,NULL);
INSERT INTO work VALUES('doi:10.1007/s00209-010-0770-x',2010,NULL);
INSERT INTO work VALUES('doi:10.1007/s00209-018-2185-z',2019,NULL);
INSERT INTO work VALUES('doi:10.1007/s00236-005-0177-z',2005,'doi:10.1007/978-3-030-99253-8_18');
INSERT INTO work VALUES('doi:10.1016/0012-365x(75)90103-x',1975,NULL);
INSERT INTO work VALUES('doi:10.1016/0022-4049(76)90013-x',1976,NULL);
INSERT INTO work VALUES('doi:10.1016/0168-0072(86)90053-9',1986,NULL);
INSERT INTO work VALUES('doi:10.1016/0304-3975(82)90026-3',1982,NULL);
INSERT INTO work VALUES('doi:10.1016/0304-3975(92)00023-k',1994,NULL);
INSERT INTO work VALUES('doi:10.1016/0304-3975(93)90054-w',1993,NULL);
INSERT INTO work VALUES('doi:10.1016/0304-3975(93)90091-7',1993,NULL);
INSERT INTO work VALUES('doi:10.1016/0898-1221(81)90008-0',1981,NULL);
INSERT INTO work VALUES('doi:10.1016/1385-7258(72)90034-0',1972,'doi:10.1016/0890-5401(91');
INSERT INTO work VALUES('doi:10.1016/b978-0-08-012975-4.50028-x',1970,NULL);
INSERT INTO work VALUES('doi:10.1016/j.aim.2018.03.016',2018,'doi:10.1016/j.aim.2020.107267');
INSERT INTO work VALUES('doi:10.1016/j.ic.2006.12.002',2007,NULL);
INSERT INTO work VALUES('doi:10.1016/j.jpaa.2022.107306',2023,NULL);
INSERT INTO work VALUES('doi:10.1016/j.jpdc.2026.105238',2026,NULL);
INSERT INTO work VALUES('doi:10.1016/j.peva.2014.07.016',2014,'doi:10.1145/3584663');
INSERT INTO work VALUES('doi:10.1016/j.tcs.2017.02.009',2017,NULL);
INSERT INTO work VALUES('doi:10.1016/j.tcs.2022.01.017',2022,NULL);
INSERT INTO work VALUES('doi:10.1016/s0012-365x(98)00319-7',1999,'doi:10.1007/11604686_37');
INSERT INTO work VALUES('doi:10.1016/s0049-237x(09)70189-2',1982,NULL);
INSERT INTO work VALUES('doi:10.1016/s0304-3975(97)00143-6',1998,NULL);
INSERT INTO work VALUES('doi:10.1016/s0747-7171(87)80022-6',1987,'doi:10.1007/3-540-56393-8_13');
INSERT INTO work VALUES('doi:10.1017/9781009498968',2025,NULL);
INSERT INTO work VALUES('doi:10.1017/9781316219317',2017,NULL);
INSERT INTO work VALUES('doi:10.1017/cbo9781139084673',2013,NULL);
INSERT INTO work VALUES('doi:10.1017/cbo9781139172752',1998,NULL);
INSERT INTO work VALUES('doi:10.1017/s0956796807006223',2007,'doi:10.1145/1411304.1411311');
INSERT INTO work VALUES('doi:10.1017/s0956796814000264',2014,'doi:10.1145/2784731.2784738');
INSERT INTO work VALUES('doi:10.1017/s0956796818000023',2018,'doi:10.1145/3414080.3414086');
INSERT INTO work VALUES('doi:10.1017/s095679681800014x',2018,NULL);
INSERT INTO work VALUES('doi:10.1017/s0956796820000076',2021,NULL);
INSERT INTO work VALUES('doi:10.1017/s0956796898003153',1998,NULL);
INSERT INTO work VALUES('doi:10.1017/s0956796899003500',1999,NULL);
INSERT INTO work VALUES('doi:10.1017/s0960129503004122',2004,'doi:10.1007/11916277_18');
INSERT INTO work VALUES('doi:10.1017/s0960129514000565',2014,'doi:10.4310/hha.2017.v19.n2.a12');
INSERT INTO work VALUES('doi:10.1017/s0960129522000123',2022,NULL);
INSERT INTO work VALUES('doi:10.1017/s0960129522000317',2022,'doi:10.1007/978-3-031-94706-3_2');
INSERT INTO work VALUES('doi:10.1023/a:1023064908962',2003,'doi:10.2168/lmcs-9(4:23');
INSERT INTO work VALUES('doi:10.1051/ita:2002009',2002,NULL);
INSERT INTO work VALUES('doi:10.1051/ita:2004015',2004,'doi:10.2168/lmcs-4(2:3');
INSERT INTO work VALUES('doi:10.1073/pnas.50.5.869',1963,'doi:10.1007/bfb0077116');
INSERT INTO work VALUES('doi:10.1090/s0002-9947-00-02653-2',2000,NULL);
INSERT INTO work VALUES('doi:10.1093/logcom/1.4.497',1991,'doi:10.1017/s1471068421000533');
INSERT INTO work VALUES('doi:10.1093/logcom/exp033',2009,NULL);
INSERT INTO work VALUES('doi:10.1098/rsta.2005.1650',2005,NULL);
INSERT INTO work VALUES('doi:10.1109/lics.1999.782635',2003,'doi:10.1145/1206035.1206037');
INSERT INTO work VALUES('doi:10.1109/lics52264.2021.9470758',2021,NULL);
INSERT INTO work VALUES('doi:10.1109/tpds.2020.2984632',2020,'doi:10.1109/ipccc55026.2022.9894295');
INSERT INTO work VALUES('doi:10.1142/s0219199720500558',2020,NULL);
INSERT INTO work VALUES('doi:10.1145/1187436.1210590',2007,NULL);
INSERT INTO work VALUES('doi:10.1145/1462166.1462167',2009,NULL);
INSERT INTO work VALUES('doi:10.1145/174675.176926',1994,NULL);
INSERT INTO work VALUES('doi:10.1145/174675.176927',1994,'doi:10.1145/604131.604151');
INSERT INTO work VALUES('doi:10.1145/1863543.1863547',2010,NULL);
INSERT INTO work VALUES('doi:10.1145/199448.199476',1995,NULL);
INSERT INTO work VALUES('doi:10.1145/2034675.2034690',2011,NULL);
INSERT INTO work VALUES('doi:10.1145/2433396.2433409',2013,NULL);
INSERT INTO work VALUES('doi:10.1145/2500365.2500606',2013,NULL);
INSERT INTO work VALUES('doi:10.1145/2535838.2535851',2014,'doi:10.1109/eurospw.2018.00010');
INSERT INTO work VALUES('doi:10.1145/2660193.2660195',2014,'doi:10.1145/3485525');
INSERT INTO work VALUES('doi:10.1145/28395.28434',1987,NULL);
INSERT INTO work VALUES('doi:10.1145/2951913.2951917',2016,'doi:10.1017/s095679681800014x');
INSERT INTO work VALUES('doi:10.1145/2976022.2976033',2016,NULL);
INSERT INTO work VALUES('doi:10.1145/3009837.3009900',2016,'doi:10.1145/3704909');
INSERT INTO work VALUES('doi:10.1145/3110250',2017,NULL);
INSERT INTO work VALUES('doi:10.1145/321250.321253',1965,'doi:10.1007/978-3-642-81955-1_9');
INSERT INTO work VALUES('doi:10.1145/321812.321820',1974,NULL);
INSERT INTO work VALUES('doi:10.1145/322217.322230',1980,NULL);
INSERT INTO work VALUES('doi:10.1145/3236770',2018,'doi:10.1017/s0956796819000182');
INSERT INTO work VALUES('doi:10.1145/3236774',2018,'doi:10.1017/s0956796820000088');
INSERT INTO work VALUES('doi:10.1145/3290327',2019,'doi:10.1145/3586048');
INSERT INTO work VALUES('doi:10.1145/3290341',2019,NULL);
INSERT INTO work VALUES('doi:10.1145/3314221.3314631',2019,NULL);
INSERT INTO work VALUES('doi:10.1145/3341708',2019,NULL);
INSERT INTO work VALUES('doi:10.1145/3341714',2019,NULL);
INSERT INTO work VALUES('doi:10.1145/3371126',2019,NULL);
INSERT INTO work VALUES('doi:10.1145/3373718.3394762',2020,NULL);
INSERT INTO work VALUES('doi:10.1145/3428194',2020,NULL);
INSERT INTO work VALUES('doi:10.1145/3450952',2021,NULL);
INSERT INTO work VALUES('doi:10.1145/3452143.3465552',2021,NULL);
INSERT INTO work VALUES('doi:10.1145/3474834',2021,NULL);
INSERT INTO work VALUES('doi:10.1145/3485513',2021,NULL);
INSERT INTO work VALUES('doi:10.1145/3502719',2022,NULL);
INSERT INTO work VALUES('doi:10.1145/351240.351262',2000,'doi:10.48550/arxiv.1006.2283');
INSERT INTO work VALUES('doi:10.1145/3531130.3533365',2022,'doi:10.22331/q-2026-01-19-1972');
INSERT INTO work VALUES('doi:10.1145/3547641',2022,'doi:10.1145/3674648');
INSERT INTO work VALUES('doi:10.1145/3586048',2023,'doi:10.1145/3689728');
INSERT INTO work VALUES('doi:10.1145/359138.359142',1979,NULL);
INSERT INTO work VALUES('doi:10.1145/3622837',2023,NULL);
INSERT INTO work VALUES('doi:10.1145/3632910',2024,NULL);
INSERT INTO work VALUES('doi:10.1145/3632920',2024,NULL);
INSERT INTO work VALUES('doi:10.1145/3674639',2024,'doi:10.1145/3720507');
INSERT INTO work VALUES('doi:10.1145/3689755',2024,NULL);
INSERT INTO work VALUES('doi:10.1145/368996.369025',1962,NULL);
INSERT INTO work VALUES('doi:10.1145/3704912',2025,'doi:10.1145/3776732');
INSERT INTO work VALUES('doi:10.1145/3720434',2025,NULL);
INSERT INTO work VALUES('doi:10.1145/3747532',2025,NULL);
INSERT INTO work VALUES('doi:10.1145/3763117',2025,NULL);
INSERT INTO work VALUES('doi:10.1145/3763182',2025,NULL);
INSERT INTO work VALUES('doi:10.1145/3776685',2026,NULL);
INSERT INTO work VALUES('doi:10.1145/3776695',2026,NULL);
INSERT INTO work VALUES('doi:10.1145/3828688',2026,NULL);
INSERT INTO work VALUES('doi:10.1145/3839474',2026,NULL);
INSERT INTO work VALUES('doi:10.1145/502034.502052',2001,'doi:10.1145/2517349.2522721');
INSERT INTO work VALUES('doi:10.1145/581478.581501',2002,NULL);
INSERT INTO work VALUES('doi:10.1145/604131.604151',2003,'doi:10.1145/1291151.1291196');
INSERT INTO work VALUES('doi:10.1145/800194.805852',1972,NULL);
INSERT INTO work VALUES('doi:10.1145/96709.96718',1990,NULL);
INSERT INTO work VALUES('doi:10.17487/rfc8089',2017,NULL);
INSERT INTO work VALUES('doi:10.17487/rfc9923',2026,NULL);
INSERT INTO work VALUES('doi:10.2140/agt.2021.21.1267',2021,'doi:10.1090/conm/838/16737');
INSERT INTO work VALUES('doi:10.2168/lmcs-11(1:3)2015',2015,NULL);
INSERT INTO work VALUES('doi:10.2168/lmcs-11(4:3)2015',2015,NULL);
INSERT INTO work VALUES('doi:10.2168/lmcs-4(1:9)2008',2008,'doi:10.2168/lmcs-12(2:5');
INSERT INTO work VALUES('doi:10.2168/lmcs-9(4:23)2013',2013,'doi:10.1017/s0956796816000320');
INSERT INTO work VALUES('doi:10.23638/lmcs-16(1:10)2020',2020,NULL);
INSERT INTO work VALUES('doi:10.23658/taltech.47/2025',2025,NULL);
INSERT INTO work VALUES('doi:10.32408/compositionality-4-5',2022,NULL);
INSERT INTO work VALUES('doi:10.4171/dm/392',2013,NULL);
INSERT INTO work VALUES('doi:10.4204/eptcs.275.6',2018,NULL);
INSERT INTO work VALUES('doi:10.4204/eptcs.323.4',2020,'doi:10.1016/j.jlamp.2023.100893');
INSERT INTO work VALUES('doi:10.4204/eptcs.372.23',2022,'doi:10.1007/s13348-024-00446-8');
INSERT INTO work VALUES('doi:10.4204/eptcs.380.7',2023,'doi:10.23658/taltech.47/2025');
INSERT INTO work VALUES('doi:10.4230/lipics.calco.2019.20',2019,NULL);
INSERT INTO work VALUES('doi:10.4230/lipics.concur.2024.35',2024,NULL);
INSERT INTO work VALUES('doi:10.4230/lipics.csl.2024.19',2023,NULL);
INSERT INTO work VALUES('doi:10.4230/lipics.fscd.2022.22',2022,NULL);
INSERT INTO work VALUES('doi:10.4230/lipics.fscd.2023.17',2023,NULL);
INSERT INTO work VALUES('doi:10.4230/lipics.fscd.2024.10',2024,NULL);
INSERT INTO work VALUES('doi:10.4230/lipics.fscd.2026.18',2026,NULL);
INSERT INTO work VALUES('doi:10.4230/lipics.lics.2026.58',2026,NULL);
INSERT INTO work VALUES('doi:10.4230/lipics.mfcs.2024.49',2025,'doi:10.1145/3837064');
INSERT INTO work VALUES('doi:10.4230/lipics.mfcs.2024.57',2024,NULL);
INSERT INTO work VALUES('doi:10.4230/lipics.rta.2013.223',2013,'doi:10.1017/9781009498968');
INSERT INTO work VALUES('doi:10.4230/lipics.types.2015.5',2018,'doi:10.46298/lmcs-18(1:28');
INSERT INTO work VALUES('doi:10.4230/lipics.types.2024.9',2025,NULL);
INSERT INTO work VALUES('doi:10.4310/hha.2018.v20.n2.a11',2018,NULL);
INSERT INTO work VALUES('doi:10.4310/hha.2022.v24.n1.a16',2022,NULL);
INSERT INTO work VALUES('doi:10.46298/lmcs-17(4:5)2021',2021,NULL);
INSERT INTO work VALUES('doi:10.46298/lmcs-18(1:10)2022',2022,NULL);
INSERT INTO work VALUES('doi:10.5381/jot.2022.21.2.a2',2022,NULL);
INSERT INTO work VALUES('doi:10.70675/7bb9b51ezf689z4cb5z8d80z794397b5f052',2024,NULL);
INSERT INTO work VALUES('doi:10.70675/ac84f832z1632z49d3za008zba5df4cfed2e',2025,NULL);
CREATE TABLE fidelity(
  -- A site the citation refresh has read against the newest work stating
  -- what it builds, written by hand. The site is a crate's directory under
  -- crates/ and its module's path, empty for the crate root, or `corpus` and
  -- a source's path under corpus/.
  crate      TEXT NOT NULL CONSTRAINT "crate is a directory under crates/ or corpus" CHECK(crate = 'corpus' OR (crate GLOB '[a-z]*-[a-z]*' AND crate NOT GLOB '*[^a-z0-9-]*')),
  module     TEXT NOT NULL,
  -- The work the site cited before the refresh, by its key or its locator.
  old        TEXT NOT NULL CONSTRAINT "old is one word" CHECK(old <> '' AND instr(old, ' ') = 0 AND instr(old, char(9)) = 0),
  -- How the site's code stands to the newest work:
  --   historical  it follows the old work's framing, which the newest
  --               supersedes, and `follow_up` names the refactor;
  --   current     it already follows the newest work;
  --   synthesis   it departs from both on purpose, and its module's
  --               documentation says why.
  verdict    TEXT NOT NULL CONSTRAINT "verdict is historical, current or synthesis" CHECK(verdict IN ('historical', 'current', 'synthesis')),
  -- The issue that brings a historical site to the newest work's framing.
  follow_up  INTEGER CONSTRAINT "follow_up is an issue number" CHECK(follow_up IS NULL OR follow_up > 0),
  -- Every work traced from the newest one, cited or not, by key or locator,
  -- one space between each; NULL before the trace.
  followed   TEXT,
  -- Whether the newest work states the whole of what the site builds, or a
  -- narrower case of it.
  scope      TEXT NOT NULL CONSTRAINT "scope is whole or narrower" CHECK(scope IN ('whole', 'narrower')),
  -- For a narrower newest work: the key of the central statement it
  -- specialises, which the site cites as `anchor`, or the statement that the
  -- citation window holds none.
  anchor     TEXT CONSTRAINT "anchor is one word" CHECK(anchor IS NULL OR (anchor <> '' AND instr(anchor, ' ') = 0)),
  unanchored TEXT,
  PRIMARY KEY(crate, module, old),
  CONSTRAINT "a site names an anchor or states that none exists, not both" CHECK(anchor IS NULL OR unanchored IS NULL)
) WITHOUT ROWID;
CREATE TABLE reading(
  -- A reading of a source against a site, written by hand through `mise run
  -- refs:read`: the key, the crate and the module of the `reference` row
  -- that the site's citation makes, the commit checked out, the day, and the
  -- blob id of the module's source then.
  key         TEXT NOT NULL,
  crate       TEXT NOT NULL,
  module      TEXT NOT NULL,
  read_commit TEXT NOT NULL CONSTRAINT "read_commit is a full commit id" CHECK(length(read_commit) = 40 AND read_commit NOT GLOB '*[^0-9a-f]*'),
  read_date   TEXT NOT NULL CONSTRAINT "read_date is YYYY-MM-DD" CHECK(read_date GLOB '[0-9][0-9][0-9][0-9]-[0-1][0-9]-[0-3][0-9]'),
  read_blob   TEXT NOT NULL CONSTRAINT "read_blob is a full blob id" CHECK(length(read_blob) = 40 AND read_blob NOT GLOB '*[^0-9a-f]*'),
  PRIMARY KEY(key, crate, module)
) WITHOUT ROWID;
INSERT INTO reading VALUES('Ahrens-2025-weighted_rewriting_semiring_semantics_abstract_reduction_systems','surface-dispatcher','cells::fusion','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','cd72addbc37d1800e66d15304a1a6b424528b44d');
INSERT INTO reading VALUES('Ahrens-2025-weighted_rewriting_semiring_semantics_abstract_reduction_systems','surface-driver','','41e7653c2cfd14be3e7090ddfd3577daebc7b277','2026-11-10','35a7e9b318536185d6c4750371d64e76cd5527d3');
INSERT INTO reading VALUES('Ahrens-2025-weighted_rewriting_semiring_semantics_abstract_reduction_systems','theory-ordered-algebras','','6ac5e25f30e5d98caed7a3aa40a0e9716b3595c5','2026-11-07','f3a5c644a24d2aa271da3450ba19bc89e4317451');
INSERT INTO reading VALUES('Bakke-2026-synthetic_sierpinski_cone','theory-exact-reals','','ceaf6665d2b7506cdd0e73995ba04ec6b4e0548b','2026-11-07','9e0d29dcb41e28bf1dfa4f17bc9c76800ca3975d');
INSERT INTO reading VALUES('Barrett-2025-proof_compression_subatomic_logic_guarded_substitutions','theory-deep-inference','reduction','2cfda0a0aea4a66803f7e35f2645f0a42afba26c','2026-11-07','19fddbb1df0b47b5d8f0bb3f10320fd0cc9c0d3d');
INSERT INTO reading VALUES('Bauer-2009-dedekind_reals_abstract_stone_duality','theory-exact-reals','','ceaf6665d2b7506cdd0e73995ba04ec6b4e0548b','2026-11-07','9e0d29dcb41e28bf1dfa4f17bc9c76800ca3975d');
INSERT INTO reading VALUES('Bauer-efficient_computation_dedekind_reals','theory-exact-reals','','ceaf6665d2b7506cdd0e73995ba04ec6b4e0548b','2026-11-07','9e0d29dcb41e28bf1dfa4f17bc9c76800ca3975d');
INSERT INTO reading VALUES('Cherubini-2024-foundation_synthetic_stone_duality','theory-cellular-sheaves','','587e03d49c1c2243e10197c7debc99b281773a42','2026-11-14','f5c99f4282c43c9fa9583cccc76285890167e21c');
INSERT INTO reading VALUES('Cherubini-2024-foundation_synthetic_stone_duality','theory-shapes','formula','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','36f894989d773771961311177868caf3f968d516');
INSERT INTO reading VALUES('Cherubini-2024-foundation_synthetic_stone_duality','theory-stone-duality','','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','24bac3438243f9d8aabb12c04fbfb26c5b8416ac');
INSERT INTO reading VALUES('Courant-2026-lazy_concurrent_convertibility_checker','kernel-check-memo','','905a22c52084a861dd032122053edbd0bda46281','2026-10-26','46dd259982ca073bd7bc09a418ba63beebeda635');
INSERT INTO reading VALUES('Curry-2015-discrete_morse_theory_computing_cellular_sheaf_cohomology','theory-cellular-sheaves','reduce','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','cefb8f38f0d424c785ee151c639ea3772dacb53d');
INSERT INTO reading VALUES('Curry-2015-discrete_morse_theory_computing_cellular_sheaf_cohomology','theory-discrete-morse','reduct','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','e2806ee9859d5431b49caf4b760e4fe27ba94efa');
INSERT INTO reading VALUES('Doré-2023-computing_spaces_type_theory','theory-discrete-morse','','b86e39667e44b2b3b2eccf368b0f4aa1db2ae3b6','2026-11-07','f391d073a4675f46d2dafc39233a201a3f0149fa');
INSERT INTO reading VALUES('Doré-2023-computing_spaces_type_theory','theory-discrete-morse','reduction','0f814f68e01c3855f0c5eaa765f41bc132a766e0','2026-11-07','a7c2a7c21843b7c98df5d3d4a542292e77e11ae0');
INSERT INTO reading VALUES('Doré-2023-computing_spaces_type_theory','theory-exact-reals','graph','6099d43c994e63da017541bf4588861828115dc1','2026-11-07','e18d0d9572b33421d9960d9d8bf1df8b5df19439');
INSERT INTO reading VALUES('Doré-2023-computing_spaces_type_theory','theory-shapes','formula','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','36f894989d773771961311177868caf3f968d516');
INSERT INTO reading VALUES('Doré-2026-dependent_multiplicities_dependent_linear_type_theory','core-term','','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','47750eeb9f84f45eb06c9c19ce35c51433f7b123');
INSERT INTO reading VALUES('Dybjer-2012-program_testing_meaning_explanations_intuitionistic_type_theory','core-nbe','policy','7be67563d6dd190101e3b62a9c0ed843f01a4bde','2026-10-28','e12ff420f25112f1d2b8bfc68d2f94d5964d005b');
INSERT INTO reading VALUES('Escardó-2004-synthetic_topology_data_types_classical_spaces','theory-exact-reals','','ceaf6665d2b7506cdd0e73995ba04ec6b4e0548b','2026-11-07','9e0d29dcb41e28bf1dfa4f17bc9c76800ca3975d');
INSERT INTO reading VALUES('Gavazzo-2022-quantitative_metric_rewriting_abstract_nonexpansive_graded_systems','surface-dispatcher','cells::fusion','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','cd72addbc37d1800e66d15304a1a6b424528b44d');
INSERT INTO reading VALUES('Ghrist-2022-cellular_sheaves_lattices_tarski_laplacian','theory-cellular-sheaves','','587e03d49c1c2243e10197c7debc99b281773a42','2026-11-14','f5c99f4282c43c9fa9583cccc76285890167e21c');
INSERT INTO reading VALUES('Grodin-2026-potential_functions_types','kernel-core-base','levels','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','b4d5d86272f0c379e8626491b800d6a720394e35');
INSERT INTO reading VALUES('Grodin-2026-potential_functions_types','kernel-strata','poset','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','63cf51119ea5e8cbfa160672f287983114665a83');
INSERT INTO reading VALUES('Guiraud-2019-convergent_presentations_polygraphic_resolutions_associative_algebras','theory-discrete-morse','','b86e39667e44b2b3b2eccf368b0f4aa1db2ae3b6','2026-11-07','f391d073a4675f46d2dafc39233a201a3f0149fa');
INSERT INTO reading VALUES('Hadzihasanovic-2023-higherdimensional_subdiagram_matching','surface-dispatcher','cells::fusion','586e64cdd35be5eae39e021356e86d0e26eb6462','2026-11-07','cd72addbc37d1800e66d15304a1a6b424528b44d');
INSERT INTO reading VALUES('Hadzihasanovic-2023-higherdimensional_subdiagram_matching','theory-cell-complexes','alphabet','4932b17daeb4a275c0daef9c897b1675b3db7053','2026-11-07','bf6997119a02467715b6559415cec8dcf840a52a');
INSERT INTO reading VALUES('Hadzihasanovic-2023-higherdimensional_subdiagram_matching','theory-deep-inference','shift','636e467ee5712506801b88233c6fcf12fa19b076','2026-11-07','6bc30c8da526d378521d82a4fbbbe26219b64de2');
INSERT INTO reading VALUES('Hansen-2020-laplacians_cellular_sheaves_theory_applications','theory-cellular-sheaves','','587e03d49c1c2243e10197c7debc99b281773a42','2026-11-14','f5c99f4282c43c9fa9583cccc76285890167e21c');
INSERT INTO reading VALUES('Jeandel-2018-complete_axiomatisation_zxcalculus_clifford+t_quantum_mechanics','theory-ordered-algebras','','6ac5e25f30e5d98caed7a3aa40a0e9716b3595c5','2026-11-07','f3a5c644a24d2aa271da3450ba19bc89e4317451');
INSERT INTO reading VALUES('Kovács-2022-staged_compilation_twolevel_type_theorya','surface-grammar','surface::term','db60bc4ed0a81c61929941b9f01c0256c2af1168','2026-11-02','bb7ea16a861957dfc8f4ee999b33a4d61bed1863');
INSERT INTO reading VALUES('Li-2024-nominal_approach_probabilistic_separation_logic','theory-probability','','3733211b5af43c30d9e4cebee16c666287f095b4','2026-11-07','234f19cce3f96fa69a4cea4c6ff5b3cbaadb754d');
INSERT INTO reading VALUES('Ljungström-2025-computational_synthetic_cohomology_theory_homotopy_type_theory','theory-cellular-sheaves','','587e03d49c1c2243e10197c7debc99b281773a42','2026-11-14','f5c99f4282c43c9fa9583cccc76285890167e21c');
INSERT INTO reading VALUES('Plotkin-2013-handling_algebraic_effects','core-checker-bridge','bridge','d38ffeaccc6639cb2a02ad7a18fd25b0d03a892d','2026-10-29','663ac54adb8b393f7ff7154d3c59eac7fcf7c44c');
INSERT INTO reading VALUES('Pruiksma-2022-back_futures','runtime-emitter','cut','fc0387766eac4f5ffc7dc1a2622e7670e587c7b7','2026-10-29','40551b1269e78f7ae38d6f550f8e1e04de8adf84');
INSERT INTO reading VALUES('Racordon-2020-formal_definition_swifts_value_semantics','runtime-emitter','run','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','9b28997d81f735c6cf7080802cf6bf58d95c2d97');
INSERT INTO reading VALUES('Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory','core-sequent','','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','60aac255e127288c58c270ac17cda0fcceb28445');
INSERT INTO reading VALUES('Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory','core-term','memory','0c8914ce9689f88b9bb86ae0349f1c162b8a3d68','2026-10-27','1b6091fc402781549385efd19a99c87b29c0fe2d');
INSERT INTO reading VALUES('Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory','core-term','world','775f54d99d0fd78230b9e5afa51d674039fd0fd5','2026-10-27','1ed0fa5ee5623d4bb42b3ae9c5791ccaf6a2e722');
INSERT INTO reading VALUES('Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory','runtime-emitter','','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','36029ff370a4f09ce9349dce5f00d2c8f44f78d3');
INSERT INTO reading VALUES('Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory','runtime-emitter','crossing','5630fb4598d9bfdaafb4ddf50a51da4d99bc1bb6','2026-10-27','e18d7dd7526358fee7a1b74909f23cbf4c6580e3');
INSERT INTO reading VALUES('Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory','runtime-emitter','run','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','9b28997d81f735c6cf7080802cf6bf58d95c2d97');
INSERT INTO reading VALUES('Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory','runtime-emitter','world','ac6d1b53b231cccc887d0b195e7f255cdf667edf','2026-10-28','e466a5329dce861389d9d3fa2c2eac81cce5b0c5');
INSERT INTO reading VALUES('Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory','storage-artifact','','0c8914ce9689f88b9bb86ae0349f1c162b8a3d68','2026-10-27','ef9bb00ebb8083a526b1a08c9c150047066064d8');
INSERT INTO reading VALUES('Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory','storage-chunker','','0c8914ce9689f88b9bb86ae0349f1c162b8a3d68','2026-10-27','6227fbbd288c00a8d4056ac5d9aad7844826e3bb');
INSERT INTO reading VALUES('Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory','storage-records','','0c8914ce9689f88b9bb86ae0349f1c162b8a3d68','2026-10-27','d79616b7f14951779128a95cb9a8bf64be0e10e6');
INSERT INTO reading VALUES('Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory','storage-values','','0c8914ce9689f88b9bb86ae0349f1c162b8a3d68','2026-10-27','8b696948ad821b58ff0396a795d5884518aaa6b2');
INSERT INTO reading VALUES('Simpson-2026-equivalence_conditional_independence_atomic_sheaf_logic','theory-probability','','3733211b5af43c30d9e4cebee16c666287f095b4','2026-11-07','234f19cce3f96fa69a4cea4c6ff5b3cbaadb754d');
INSERT INTO reading VALUES('Sterling-2026-domains_classifying_topoi','theory-shapes','formula','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','36f894989d773771961311177868caf3f968d516');
INSERT INTO reading VALUES('Sterling-2026-domains_classifying_topoi','theory-stone-duality','','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','24bac3438243f9d8aabb12c04fbfb26c5b8416ac');
INSERT INTO reading VALUES('Tarau-2008-functional_hitchhikers_guide_hereditarily_finite_sets_ackermann_encodings_pairing_functions','theory-exact-reals','ackermann','578de397edfc0e1cf510674eb9325ce9f7418ab6','2026-11-07','b94955e326d1fedb2039fe89e7736d72a76a471e');
INSERT INTO reading VALUES('Tarau-2008-ranking_catamorphisms_unranking_anamorphisms_hereditarily_finite_datatypes','theory-exact-reals','ackermann','578de397edfc0e1cf510674eb9325ce9f7418ab6','2026-11-07','b94955e326d1fedb2039fe89e7736d72a76a471e');
INSERT INTO reading VALUES('Taylor-2010-lambda_calculus_real_analysis','theory-exact-reals','','ceaf6665d2b7506cdd0e73995ba04ec6b4e0548b','2026-11-07','9e0d29dcb41e28bf1dfa4f17bc9c76800ca3975d');
INSERT INTO reading VALUES('Wood-2024-framework_semiringannotated_type_systems','core-checker','','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','9d949b38848b499a5cfd920ea5c04c5cc8630d6e');
INSERT INTO reading VALUES('Wood-2024-framework_semiringannotated_type_systems','core-checker-base','access','586e64cdd35be5eae39e021356e86d0e26eb6462','2026-11-07','a6d3b5e613083b88b2f9096f172eabdc6890b4b7');
INSERT INTO reading VALUES('Wood-2024-framework_semiringannotated_type_systems','core-term','','98276fb75d8d6879c2bf6acfc66587e60fcae258','2026-11-07','47750eeb9f84f45eb06c9c19ce35c51433f7b123');
INSERT INTO reading VALUES('Wood-2024-framework_semiringannotated_type_systems','core-term','memory','586e64cdd35be5eae39e021356e86d0e26eb6462','2026-11-07','7928901ea52703359b926253920e6bb1f55c544e');
INSERT INTO reading VALUES('Wood-2024-framework_semiringannotated_type_systems','theory-ordered-algebras','','6ac5e25f30e5d98caed7a3aa40a0e9716b3595c5','2026-11-07','f3a5c644a24d2aa271da3450ba19bc89e4317451');
INSERT INTO reading VALUES('Wood-2024-framework_semiringannotated_type_systems','theory-ordered-algebras','usage','586e64cdd35be5eae39e021356e86d0e26eb6462','2026-11-07','183e44786766ce911063ac7b29f6a0f1d2c75613');
INSERT INTO reading VALUES('arXiv:2005.04453','theory-deep-inference','','b86e39667e44b2b3b2eccf368b0f4aa1db2ae3b6','2026-11-07','604a0db1784fec8724108b5b6bd8989bfcad061a');
INSERT INTO reading VALUES('arXiv:2104.14686','theory-deep-inference','','b86e39667e44b2b3b2eccf368b0f4aa1db2ae3b6','2026-11-07','604a0db1784fec8724108b5b6bd8989bfcad061a');
INSERT INTO reading VALUES('arXiv:2505.20009','theory-deep-inference','','b86e39667e44b2b3b2eccf368b0f4aa1db2ae3b6','2026-11-07','604a0db1784fec8724108b5b6bd8989bfcad061a');
INSERT INTO reading VALUES('arXiv:2601.08071','core-sequent','','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','60aac255e127288c58c270ac17cda0fcceb28445');
INSERT INTO reading VALUES('arXiv:2601.08071','runtime-stencils','','66cbc25bfce14f56fb70ecba36ab78d735b45ea7','2026-10-26','24b6c43aecf1cda8f417f5238cc1b69900e9febb');
INSERT INTO reading VALUES('doi:10.1007/3-540-48959-2_17','core-sequent','','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','60aac255e127288c58c270ac17cda0fcceb28445');
INSERT INTO reading VALUES('doi:10.1017/s0956796818000023','core-sequent','','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','60aac255e127288c58c270ac17cda0fcceb28445');
INSERT INTO reading VALUES('doi:10.1017/s0960129522000317','theory-deep-inference','','b86e39667e44b2b3b2eccf368b0f4aa1db2ae3b6','2026-11-07','604a0db1784fec8724108b5b6bd8989bfcad061a');
INSERT INTO reading VALUES('doi:10.1109/lics52264.2021.9470758','theory-deep-inference','','b86e39667e44b2b3b2eccf368b0f4aa1db2ae3b6','2026-11-07','604a0db1784fec8724108b5b6bd8989bfcad061a');
INSERT INTO reading VALUES('doi:10.1145/3485513','runtime-emitter','','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','36029ff370a4f09ce9349dce5f00d2c8f44f78d3');
INSERT INTO reading VALUES('doi:10.1145/351240.351262','core-sequent','','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','60aac255e127288c58c270ac17cda0fcceb28445');
INSERT INTO reading VALUES('doi:10.1145/3674639','core-sequent','','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','60aac255e127288c58c270ac17cda0fcceb28445');
INSERT INTO reading VALUES('doi:10.2168/lmcs-4(1:9)2008','theory-deep-inference','','b86e39667e44b2b3b2eccf368b0f4aa1db2ae3b6','2026-11-07','604a0db1784fec8724108b5b6bd8989bfcad061a');
INSERT INTO reading VALUES('doi:10.4204/eptcs.323.4','theory-deep-inference','','b86e39667e44b2b3b2eccf368b0f4aa1db2ae3b6','2026-11-07','604a0db1784fec8724108b5b6bd8989bfcad061a');
INSERT INTO reading VALUES('doi:10.4204/eptcs.372.23','theory-deep-inference','','b86e39667e44b2b3b2eccf368b0f4aa1db2ae3b6','2026-11-07','604a0db1784fec8724108b5b6bd8989bfcad061a');
INSERT INTO reading VALUES('doi:10.4230/lipics.fscd.2022.22','theory-deep-inference','','b86e39667e44b2b3b2eccf368b0f4aa1db2ae3b6','2026-11-07','604a0db1784fec8724108b5b6bd8989bfcad061a');
INSERT INTO reading VALUES('vault:01a12723-951b-7183-87d8-4fbc83c6a779','theory-deep-inference','reduction','2cfda0a0aea4a66803f7e35f2645f0a42afba26c','2026-11-07','19fddbb1df0b47b5d8f0bb3f10320fd0cc9c0d3d');
INSERT INTO reading VALUES('vault:01a16be2-3ad1-73e2-9e54-d28a053edcaa','core-checker-bridge','template::memo','c4675519f2fc68f6e8c289bbc29de0eae3abdfc7','2026-10-29','21da273baaf8fa8b1851c07f04df073e5f74b03c');
INSERT INTO reading VALUES('vault:01a16be2-3ad1-73e2-9e54-d28a053edcaa','kernel-core','descent','c4675519f2fc68f6e8c289bbc29de0eae3abdfc7','2026-10-29','f69d6a7559364f8975c6703d516f594e90adc0e7');
INSERT INTO reading VALUES('vault:01a178aa-4bbc-7842-9a60-d11551c41e06','core-incremental','record','c40ef5389636232e5a082aea52516ebbd7b1e284','2026-10-30','e4699f0cc9f993e9055183b01e33b4d75c4ed6b5');
INSERT INTO reading VALUES('vault:01a178aa-4bbc-7842-9a60-d11551c41e06','core-publish','','2e505aca52c720dd0eabb9d39ab037f3fdde7c84','2026-11-14','b0505dedc870b4b2afdc1a763c428070cce70e63');
INSERT INTO reading VALUES('vault:01a178aa-5f59-7323-a77d-6f8114cedbba','core-checker-base','fill','f5c6fcb3d6e11921354cb06ce23eed12219e5134','2026-10-30','8fab72057caf7d961aa5f6b3ba9ab565e2f15c97');
INSERT INTO reading VALUES('vault:01a178aa-608d-75d0-8f71-e6fe4289f327','core-sequent','store','40910e71052bab6fb695592650b018c4e9d0b615','2026-10-27','81f38554c102ce824ddb881d6d39e30719eb7a04');
INSERT INTO reading VALUES('vault:01a178aa-608d-75d0-8f71-e6fe4289f327','runtime-emitter','run','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','9b28997d81f735c6cf7080802cf6bf58d95c2d97');
INSERT INTO reading VALUES('vault:01a178aa-6917-7983-b5cd-86e2af86b3ec','core-checker-bridge','bridge','e3bd8a29b81963ea819568013096a8d0070ad1c8','2026-11-12','0345924099bc356ec7f75e1fad09b7f470a21573');
INSERT INTO reading VALUES('vault:01a178aa-6917-7983-b5cd-86e2af86b3ec','core-checker-bridge','bridge::held','648841332ce3dbff019553212338953c50fc29bb','2026-11-11','b46f4bd89ad3e8b864ef529e2e01eab14be0238b');
INSERT INTO reading VALUES('vault:01a178aa-6917-7983-b5cd-86e2af86b3ec','core-checker-bridge','template::memo','c4675519f2fc68f6e8c289bbc29de0eae3abdfc7','2026-10-29','21da273baaf8fa8b1851c07f04df073e5f74b03c');
INSERT INTO reading VALUES('vault:01a178aa-6917-7983-b5cd-86e2af86b3ec','core-fork','','56d06e4fc4353f94a1a7cb1e60980f7e8d698151','2026-11-12','32fc5cc212d4e6bff1ab86eb4c75196fed8d7517');
INSERT INTO reading VALUES('vault:01a178aa-6917-7983-b5cd-86e2af86b3ec','core-nbe','policy','7be67563d6dd190101e3b62a9c0ed843f01a4bde','2026-10-28','e12ff420f25112f1d2b8bfc68d2f94d5964d005b');
INSERT INTO reading VALUES('vault:01a178aa-6917-7983-b5cd-86e2af86b3ec','kernel-core','descent','c4675519f2fc68f6e8c289bbc29de0eae3abdfc7','2026-10-29','f69d6a7559364f8975c6703d516f594e90adc0e7');
INSERT INTO reading VALUES('vault:01a178aa-6917-7983-b5cd-86e2af86b3ec','kernel-core-base','encoding','6d0adb0e7819005d199c31b3df21d4892fb55e97','2026-11-14','1c44b14a6c5313f19ce62de841b658e6141ef220');
INSERT INTO reading VALUES('vault:01a178aa-6b8e-7d60-a533-ec9379c0462a','core-fork','','2c01afb82b139b1b7efbd126352235556d625fb5','2026-11-10','e9c5d6e75bd5836e1e66d50b8de52e81839abec9');
INSERT INTO reading VALUES('vault:01a178aa-6b8e-7d60-a533-ec9379c0462a','core-sequent','','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','60aac255e127288c58c270ac17cda0fcceb28445');
INSERT INTO reading VALUES('vault:01a178aa-6b8e-7d60-a533-ec9379c0462a','core-sequent','spawn','e89a549414c477a296aac76c78cf7c326d0d2878','2026-10-29','8365195b2e813bb1e8fa80a1596772539560130b');
INSERT INTO reading VALUES('vault:01a178aa-6b8e-7d60-a533-ec9379c0462a','runtime-emitter','cut','fc0387766eac4f5ffc7dc1a2622e7670e587c7b7','2026-10-29','40551b1269e78f7ae38d6f550f8e1e04de8adf84');
INSERT INTO reading VALUES('vault:01a178aa-6b8e-7d60-a533-ec9379c0462a','runtime-emitter','run','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','9b28997d81f735c6cf7080802cf6bf58d95c2d97');
INSERT INTO reading VALUES('vault:01a178aa-a419-7ab1-82e7-40a4f95938c6','theory-exact-reals','','ceaf6665d2b7506cdd0e73995ba04ec6b4e0548b','2026-11-07','9e0d29dcb41e28bf1dfa4f17bc9c76800ca3975d');
INSERT INTO reading VALUES('vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f','core-incremental','record','c40ef5389636232e5a082aea52516ebbd7b1e284','2026-10-30','e4699f0cc9f993e9055183b01e33b4d75c4ed6b5');
INSERT INTO reading VALUES('vault:01a178aa-d585-7822-9cf0-40459729a925','surface-dispatcher','package','789bc36ba84f20d6634372c6b1f1a66e5c430e92','2026-10-27','20e46b8104c5c27d7eafb30d517d4929d769231e');
INSERT INTO reading VALUES('vault:01a178aa-d585-7822-9cf0-40459729a925','surface-dispatcher','workspace','2ced5da8a41bbf07bfb346a91b1c898985dcd293','2026-10-28','ec86c18a244f7869da25774f1cd9e8c036e54687');
INSERT INTO reading VALUES('vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c','core-sequent','store','40910e71052bab6fb695592650b018c4e9d0b615','2026-10-27','81f38554c102ce824ddb881d6d39e30719eb7a04');
INSERT INTO reading VALUES('vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c','runtime-emitter','crossing','5630fb4598d9bfdaafb4ddf50a51da4d99bc1bb6','2026-10-27','e18d7dd7526358fee7a1b74909f23cbf4c6580e3');
INSERT INTO reading VALUES('vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c','runtime-emitter','run','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','9b28997d81f735c6cf7080802cf6bf58d95c2d97');
INSERT INTO reading VALUES('vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c','runtime-emitter','world','ac6d1b53b231cccc887d0b195e7f255cdf667edf','2026-10-28','e466a5329dce861389d9d3fa2c2eac81cce5b0c5');
INSERT INTO reading VALUES('vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c','runtime-net','worlds','daeb019c78602ef2ece79a9d2b4eddc95b845090','2026-10-28','d4e403dc44a1660c699c0eeccee846f3425d6c63');
INSERT INTO reading VALUES('vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c','surface-driver','','41e7653c2cfd14be3e7090ddfd3577daebc7b277','2026-11-10','35a7e9b318536185d6c4750371d64e76cd5527d3');
INSERT INTO reading VALUES('vault:01a178ab-289d-7702-b010-1c47ae9fd427','core-nbe','eval::words','dee75f0cb20c2c058c0bd65d041bd21be86a1f8d','2026-11-11','e0765a6ce0b92e8eddd2f8b9addb1f4a0fa2dbb7');
INSERT INTO reading VALUES('vault:01a178ab-289d-7702-b010-1c47ae9fd427','kernel-core','words','dee75f0cb20c2c058c0bd65d041bd21be86a1f8d','2026-11-11','e6fb39db6e367e88d4954c13c2ef1020288c881a');
INSERT INTO reading VALUES('vault:01a178ab-289d-7702-b010-1c47ae9fd427','kernel-term','presented','aa4429d8006a3ce951113857ed0ab3bcb934b4f3','2026-11-11','abbc52ff30c040a974580ca302925cd5379d7dad');
INSERT INTO reading VALUES('vault:01a17f02-42f0-7920-bede-5615d3bade8c','runtime-emitter','','369732040a5bf26e640bab58f3d89bd9f4368110','2026-10-29','36029ff370a4f09ce9349dce5f00d2c8f44f78d3');
INSERT INTO reading VALUES('vault:01a17f02-42f0-7920-bede-5615d3bade8c','surface-dispatcher','manifold','6478f18ac13e022b0020fc99dc160e5ebbbc6e77','2026-11-10','16ae9d0a7483dddae61450dcbff1145e158f5243');
INSERT INTO reading VALUES('vault:01a1813c-69c4-7402-97c9-fd16b5893f9f','core-sequent','store','147a8d90f69d3fde2aae520e8c2048e101737ff1','2026-10-29','b8ab7377776615735038ee8a68cfbba2fa0526ae');
INSERT INTO reading VALUES('vault:01a1813c-69c4-7402-97c9-fd16b5893f9f','runtime-emitter','run','147a8d90f69d3fde2aae520e8c2048e101737ff1','2026-10-29','435bb1bdb63e5c693f48e4c34d2ea6bc18afcda8');
INSERT INTO reading VALUES('vault:01a1813c-69c4-7402-97c9-fd16b5893f9f','runtime-stencils','transitions','147a8d90f69d3fde2aae520e8c2048e101737ff1','2026-10-29','5798eb33d59350803c0f1f778926862d42f9727f');
INSERT INTO reading VALUES('vault:01a183de-4ab1-7660-a88a-04b9e8d318e3','core-nbe','readback','3ac0ff70e3c295db32ad698004431dd31f0601c6','2026-10-29','157acf4928483206c8d9f819971ec7e8284c5154');
INSERT INTO reading VALUES('vault:01a183de-4ab1-7660-a88a-04b9e8d318e3','core-nbe-base','closure','1d1ac3fa78df454c4a15cbc9a2124dbe6e94186d','2026-10-28','8a4aef58d20e532ef6cf0061b142b25438ea96f3');
INSERT INTO reading VALUES('vault:01a183de-4ab1-7660-a88a-04b9e8d318e3','kernel-core','replay::environment','1d1ac3fa78df454c4a15cbc9a2124dbe6e94186d','2026-10-28','09b037f2241cfe424dc51ce6595f10e36ed945af');
INSERT INTO reading VALUES('vault:01a1aa2d-a69c-7030-91e0-337d68d88151','theory-cellular-sheaves','','587e03d49c1c2243e10197c7debc99b281773a42','2026-11-14','f5c99f4282c43c9fa9583cccc76285890167e21c');
INSERT INTO reading VALUES('vault:01a1aa2d-a69c-7030-91e0-337d68d88151','theory-deep-inference','reduction','2cfda0a0aea4a66803f7e35f2645f0a42afba26c','2026-11-07','19fddbb1df0b47b5d8f0bb3f10320fd0cc9c0d3d');
INSERT INTO reading VALUES('vault:01a1aa2d-a69c-7030-91e0-337d68d88151','theory-discrete-morse','','b86e39667e44b2b3b2eccf368b0f4aa1db2ae3b6','2026-11-07','f391d073a4675f46d2dafc39233a201a3f0149fa');
INSERT INTO reading VALUES('vault:01a1aa2d-a69c-7030-91e0-337d68d88151','theory-discrete-morse','sum','b86e39667e44b2b3b2eccf368b0f4aa1db2ae3b6','2026-11-07','d0cdb8d1085104a2bb11fc971d543c12d4765c7e');
INSERT INTO reading VALUES('vault:01a1aa2d-a69c-7030-91e0-337d68d88151','theory-probability','','3733211b5af43c30d9e4cebee16c666287f095b4','2026-11-07','234f19cce3f96fa69a4cea4c6ff5b3cbaadb754d');
INSERT INTO reading VALUES('vault:01a1b278-4fbc-7c31-a4f3-2a171b335796','theory-exact-reals','minimal','b2f9eac7d4078d3e8ed85141317c9a171de7b4e7','2026-11-07','5348640e9c4186d136c37c2c3e79eb9872aa1cfb');
INSERT INTO reading VALUES('vault:01a1b278-54ca-7062-94f4-4c94748c971e','theory-exact-reals','minimal','b2f9eac7d4078d3e8ed85141317c9a171de7b4e7','2026-11-07','5348640e9c4186d136c37c2c3e79eb9872aa1cfb');
INSERT INTO reading VALUES('vault:01a1b278-5641-7c20-95d3-093641459620','theory-exact-reals','ackermann','578de397edfc0e1cf510674eb9325ce9f7418ab6','2026-11-07','b94955e326d1fedb2039fe89e7736d72a76a471e');
INSERT INTO reading VALUES('vault:01a1b32b-755c-7b73-85f1-3055991c2bee','theory-exact-reals','dyadic','8f97dfc1113b4fc1febb9a04e053f6cdba9f6861','2026-11-07','efc1b3ca0f4e734dbbec66e0cb9e66048f3844e8');
INSERT INTO reading VALUES('vault:01a1b53e-d768-7e62-8825-088be647563b','theory-exact-reals','recurrence','1c8ce077c60d346ee2ad18982b90b168809e8526','2026-11-07','9d0ddffe5990a84e450a607a284c76457bf5ff76');
INSERT INTO reading VALUES('vault:01a1b567-b34b-77a2-9ace-075796f0eb3e','core-checker-base','divergence','4a92e372fd0ce78fd4e257276266d7c97b0d8c38','2026-11-07','5e292eca6ae863067b2f03cb2d34ab7d50ebf993');
INSERT INTO reading VALUES('vault:01a1d7fd-eeb5-7010-80e7-df4d768b6583','kernel-core-base','encoding','6d0adb0e7819005d199c31b3df21d4892fb55e97','2026-11-14','1c44b14a6c5313f19ce62de841b658e6141ef220');
INSERT INTO reading VALUES('vault:01a1d7fd-eeb5-7010-80e7-df4d768b6583','storage-store','register','484c1e84c9b09f8a7b9c2b5df2bdccffcd8234f4','2026-11-14','ac1f2d912d69ea8a448bf8d898b0103fad6bbd47');
INSERT INTO reading VALUES('vault:01a1d8c5-08cb-7e12-a5d5-9a2ad3279160','storage-store','plane','484c1e84c9b09f8a7b9c2b5df2bdccffcd8234f4','2026-11-14','050e6297abe82c557307369b30f3a9e4023f2fdb');
INSERT INTO reading VALUES('vault:01a1d90b-b64a-7248-8f6e-e792b6e8cb9f','storage-store','plane','484c1e84c9b09f8a7b9c2b5df2bdccffcd8234f4','2026-11-14','050e6297abe82c557307369b30f3a9e4023f2fdb');
INSERT INTO reading VALUES('vault:01a1e7b4-8c77-7a81-9165-ff37ea870424','surface-lowering-capability','lower::capability','5eec36daeb530a2a2414ed09554c550498b9a52d','2026-11-19','e01349b44df85a4a17a18cf7e7221d5d14131eb7');
COMMIT;
