// <copyright>

// This file attempts to provide a simple abstraction for mapping
// keyboard and UI events to an editable element with separated model
// and view.  Getting everything working well (cut and paste, IME,
// undo) requires egregious hacks with existing browsers. There are
// three viable strategies to handle this:
//
// 1. Provide a simple implementation that lacks functionality.
// 2. Implement the egregious hacks and hide all that here.
// 3. Wait for browsers to implement sane API's for this.
//
// This interface should be reasonable in all three cases. We'll do
// strategy 1 first, because anything else would be pretty insane.

GH.InputLayer = function () {
};

// This might change a bit, to dispatch to mutiple handlers.
GH.InputLayer.prototype.set_handler = function(handler) {
    this.handler = handler;
};

// Attach the input layer to the specified element
GH.InputLayer.prototype.attach = function(element) {
    var self = this;
    element.onkeydown = function(evt) {
	self.handle_keydown(evt);
    };
    element.onkeypress = function(evt) {
	self.handle_keypress(evt);
    };
    element.onfocus = function(evt) {
	self.handler('focus', true);
    };
    element.onblur = function(evt) {
	self.handler('focus', false);
    };
};

// Todo: this isn't great on FF, keydown doesn't repeat. Possibly much of
// the functionality here should simply be moved to keypress.
GH.InputLayer.prototype.handle_keydown = function(evt) {
    var mods = '';
    if (evt.shiftKey) mods += 'S';
    if (evt.ctrlKey) mods += 'C';
    if (evt.altKey) mods += 'A';
    if (evt.metaKey) mods += 'M';
    log('keydown keyCode = ' + evt.keyCode + ', keyIdentifier = ' + evt.keyIdentifier + ', ' + mods + ', which = ' + evt.which);
    if (this.handler('keydown', evt)) {
	evt.preventDefault();
	return;
    }
    if (mods == 'C' && evt.keyCode == 86) {  // ctrl-V
	if (this.handler('paste', this.clipboard)) {
	    evt.preventDefault();
	    return;
	}
    } else if (mods == 'C' && evt.keyCode == 67) {  // ctrl-C
	this.clipboard = this.selectiontext;
	evt.preventDefault();
	return;
    } else if (mods == 'C' && evt.keyCode == 88) {  // ctrl-X
	this.clipboard = this.selectiontext;
	this.handler('cut', null);
	evt.preventDefault();
	return;
    } else if (mods == 'C' && evt.keyCode == 90) {  // ctrl-Z
	if (this.handler('undo', null)) {
	    evt.preventDefault();
	    return;
	}
    }
};

GH.InputLayer.prototype.handle_keypress = function(evt) {
    var mods = '';
    if (evt.shiftKey) mods += 'S';
    if (evt.ctrlKey) mods += 'C';
    if (evt.altKey) mods += 'A';
    if (evt.metaKey) mods += 'M';
    log('keypress keyCode = ' + evt.keyCode + ', keyIdentifier = ' + evt.keyIdentifier + ', ' + mods + ', which = ' + evt.which);
    if (evt.charCode >= 32 && evt.charCode < 127 &&
	!evt.altKey && !evt.metaKey) {
	if (this.handler('textinput', String.fromCharCode(evt.charCode))) {
	    evt.preventDefault();
	}
    }
};

GH.InputLayer.prototype.set_selection = function(text) {
    this.selectiontext = text;
};
