set +e
java -cp ~/src/tlaplus/java-tools/tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans Test.tla
java -cp ~/src/tlaplus/java-tools/tlatools/org.lamport.tlatools/dist/tla2tools.jar tla2sany.SANY Test.tla
node_modules/.bin/tree-sitter parse -q Test.tla

