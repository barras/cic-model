szURL = document.URL;
componentList = szURL.split('/');
base=(componentList.slice(0,componentList.length-1)).join('/');
newurl=base+"/../"+componentList[componentList.length-1];
document.writeln("For a light version without proofs, click <a href=\""+newurl+"\">here</a>.");
