INSERT INTO purpose VALUES('boot-data','','crate','Gives the bootstrap the data that allocates: the `boot` layer, outside the integrity and the validity walls.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('boot-data','string','module','Holds valid UTF-8 in a vector, with one zero byte after the last byte.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('boot-data','string::Rejected','enum','A write that the string buffer does not make: bytes that are not UTF-8, or a growth that the vector cannot make.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('boot-data','string::StringBuffer','struct','A string buffer in a block of one heap, the one owner of its valid UTF-8.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('boot-data','string::Unchecked','struct','A vector that does not become a string buffer, with its cause.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('boot-data','vector','module','Holds bytes in a block of the heap, with a capacity and a length.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('boot-data','vector::Refusal','enum','A growth that the vector cannot make: past the size of a layout, or refused by the heap.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('boot-data','vector::Vector','struct','A vector of bytes in a block of one heap, the one owner of its bytes.',NULL,'fits','sound',NULL);
