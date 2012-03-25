szURL = document.URL;
componentList = szURL.split('/');
base=(componentList.slice(0,componentList.length-1)).join('/');
newurl=base+"/full/"+componentList[componentList.length-1];
document.writeln("For a full version with proofs, click <a href=\""+newurl+"\">here</a>.");
