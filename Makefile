pcal:
	java -cp tla2tools.jar pcal.trans -nocfg wire.tla 

tlc2:
	java -cp tla2tools.jar tlc2.TLC -config wire.cfg wire.tla