GH.tupleUtil = {};

GH.tupleUtil.createTuple = function(tupleArray) {
	if (tupleArray.length == 0) {
		return GH.numUtil.createNum(0);
	} else if (tupleArray.length == 1) {
		return GH.numUtil.createNum(tupleArray[0]);
	} else if (tupleArray.length == 2) {
		return new GH.sExpression.createOperator('<,>',
		    [GH.numUtil.createNum(tupleArray[0]), GH.numUtil.createNum(tupleArray[1])]);
	} else if (tupleArray.length > 2) {
		var lastNum = tupleArray.pop();
		return new GH.sExpression.createOperator('<,>',
		    [GH.tupleUtil.createTuple(tupleArray), GH.numUtil.createNum(lastNum)]);
	}
};