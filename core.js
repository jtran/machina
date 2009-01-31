// Interpreter Core
// by Jonathan Tran
// http://jonnytran.com/

if (!console) {
  // Define dummy console if Firebug isn't loaded.
  var console = {
    debug: function(s) {},
    error: function(s) {},
    info:  function(s) {},
    log:   function(s) {},
    warn:  function(s) {},
  }
}

// Fix for Chrome (v1.0.154.36)
// Apparently you can not set properties to the console object in Chrome because
// it occasionally gets reset to the default.  :-(  Also, can't use the name "debug"
// for a function; apparently that is special also.
function dbg() {
  if (typeof(console.debug) == "undefined") {
    // Note: can't do arguments.join
    var a = [];
    for (var i = 0; i < arguments.length; i++) {
      a.push(arguments[i].toString());
    }
    return console.log(a.join(' '));
  }
  else {
    return console.debug.apply(console, arguments);
  }
}

// Generic equality
function equals(a, b) {
  for (var j, o = arguments, i = o.length, c = a instanceof Object; --i;)
    if (a === (b = o[i]))
      continue;
    else if (!c || !(b instanceof Object))
      return false;
    else for (j in b)
      if (j != 'meta' && !equals(a[j], b[j]))  // Don't compare metadata
        return false;
  return true;
}

// Generic object cloning
function clone(obj) {
  if (obj == null || typeof(obj) != 'object') return obj;

  var temp;
  try {
    if (obj.constructor == Exp) return cloneExp(obj);
    temp = new obj.constructor();
  }
  catch (e) {
    // Can't call constructor
    return obj;
  }

  for (var k in obj) {
    temp[k] = clone(obj[k]);
  }

  return temp;
}

function cloneExp(obj) {
  dbg("cloneExp")

  var temp = new Exp();
  
  // TODO: make transients generic, not just these fields.
  for (var k in obj) {
    if (k == 'evaled' || k == 'meta') continue;  // Don't copy transients
    temp[k] = clone(obj[k]);
  }
  temp.meta = {views: []};
  
  return temp;
}

// e.g. (For example)
// Asserts an example has an expected value
function eg(expected, v) {
  if (expected.neq(v)) {
    console.error("Test failed: expected: ", expected, '  found: ', v);
  }
  return v;
}

// Asserts that an expression has a specified type
function ofType(t, v) {
  if (t !== v.type) {
    console.error("Type assertion failed: expected: ", t, '  found: ', v.type);
  }
  return v;
}


// Global work queue
var q = [];
var newQ = [];
var pushedToQ = [];

function addToWorkQueue(f) {
  pushedToQ.push(f);
}


// The constructor for all expressions in the language.
function Exp() {
  this.type = arguments[0];
  this.meta = clone(arguments[1]);  // clone since this is an object that mutates
  var args = [];
  for (var i = 0; i + 2 < arguments.length; i++) {
    args[i] = arguments[i + 2];
  }

  this.eq = function() {
    var a = [this];
    $.each(arguments, function(i, x) {a.push(x)} );
    return equals.apply(this, a);
  }

  this.neq = function() {
    return ! this.eq.apply(this, arguments);
  }
  
  this.updateEvaled = function(v) {
    $.each(this.meta.views, function(i, view) {
      view.updateEvaled(v);
    });
  }
  
  this.toHtmlString = function() { return this.toString() }
  
  // This is a function so that cloning is easier.
  this.getChildren = function() { return [] }
  
  switch (this.type) {
  case 'NIL':
    this.className = "exp list nil";
    this.toString = function() {
      return 'nil';
    }
    break;
  
  case 'PAIR':
    this.first = args[0];
    this.second = args[1];
    this.className = "exp list pair";
    this.getChildren = function() { return [this.first, this.second] }
    this.toString = function() {
      return '(' + this.first + ', ' + this.second + ')';
    }
    this.toHtmlString = function() {
      return 'pair';
    }
    break;
  
  case 'FST':
    this.pair = args[0];
    this.className = 'exp fst';
    this.getChildren = function() { return [this.pair] }
    this.toString = function() {
      return this.pair + '.1';
    }
    this.toHtmlString = function() {
      return 'first';
    }
    break;
  
  case 'SND':
    this.pair = args[0];
    this.className = 'exp snd';
    this.getChildren = function() { return [this.pair] }
    this.toString = function() {
      return this.pair + '.2';
    }
    this.toHtmlString = function() {
      return 'second';
    }
    break;
  
  case 'INT':
    this.intVal = args[0];
    this.className = 'exp int';
    this.toString = function() {
      return this.intVal.toString(); // + ' : ' + this.type.toLowerCase();
    }
    this.toHtmlString = function() {
      return this.intVal.toString(); // + '&nbsp;:&nbsp;' + this.type.toLowerCase();
    }
    break;
  
  case 'SYM':
    this.symVal = args[0];
    this.className = 'exp sym';
    this.toString = function() {
      return this.symVal;
    }
    this.toHtmlString = function() {
      return "<i>" + this.symVal + "</i>";
    }
    break;
  
  case 'CHAN':
    this.ctx = args[0];
    this.sender = args[1];
    this.value = null;
    this.send = function(v) {
      if (isValue(v)) {
        dbg('chan was sent value', this, v);
        this.value = v;
      }
      else {
        this.sender = v;
      }
      // TODO: wake up the thread waiting?
      
      // Return true to remove this from the queue.
      return isValue(v);
    }
    this.className = 'exp chan';
    this.getChildren = function() { return [this.sender] }
    this.toString = function() {
      return "(ch " + this.sender + ")";
    }
    this.toHtmlString = function() {
      return "";
    }
    break;
  
  case 'PRIM':
    this.primOp = args[0];
    this.className = 'exp prim';
    this.toString = function() {
      return this.primOp;
    }
    break;
  
  case 'FUN':
    $.each(args[0], function(i, s) {
      ofType('SYM', s);
    });
    this.params = args[0];
    this.body = args[1];
    if (args.length > 2) {
      this.fixPoint = args[2];
    }
    this.className = 'exp fun';
    this.getChildren = function() { return [this.body] }
    this.toString = function() {
      return 'fn(' + this.params.join(',') + ')';
    }
    this.toHtmlString = function() {
      var s = '';
      if (this.fixPoint) {
        s += 'let <i>' + this.fixPoint + '</i> = ';
      }
      s += '&lambda; ' + $.map(this.params, function(s) {return "<i>" + s + "</i>"}).join(', ') + '.';
      return s;
    }
    break;
  
  case 'CLOSURE':
    this.ctx = args[0];
    this.params = args[1];
    this.body = args[2];
    this.fixPoint = args[3];
    this.className = 'exp closure';
    this.getChildren = function() { return [this.body] }
    this.toString = function() {
      return '<G, fn(' + this.params.join(',') + ')>';
    }
    this.toHtmlString = function() {
      return '&lt;&Gamma;, &lambda; ' +
        $.map(this.params, function(s) {return "<i>" + s.toHtmlString() + "</i>"}).join(', ') +
        '&gt;';
    }
    break;
  
  case 'APP':
    this.fun = args[0];
    this.args = args[1];
    this.getChildren = function() { return [this.fun, this.args] }
    this.className = 'exp app';
    this.toString = function() {
      return 'apply';
    }
    break;
  
  case 'CASE':
    this.cond = args[0];
    this.branches = args[1];
    this.className = 'exp case';
    this.getChildren = function() { return [this.cond, this.branches] }
    this.toString = function() {
      return 'case';
    }
    break;
  
  default:
    // clone calls this with 0 arguments all the time.
    if (this.type) console.warn('Unknown expression type', this.type);
  };
  
}

function ExpController() {
}

function ExpElmtView() {
  this.controller = arguments[0];
  this.model = arguments[1];
  this.children = [];
  
  this.toHtmlString = function() { return this.model.toHtmlString() }
  
  this.toElmt = function() {
    var elmt = document.createElement('div');
    $(elmt).html(this.toHtmlString());
    $.each(this.children, function(i, childView) {
      if (childView.length) {
        $.each(childView, function(j, subchildView) {
          $(elmt).append(subchildView.toElmt());
        });
      }
      else {
        $(elmt).append(childView.toElmt());
      }
    });
    elmt.className = this.model.className;
    
    this.elmt = elmt;
    return elmt;
  }
  
  this.updateEvaled = function(v) {
    this.evaled = v;
    //$(elmt).find('.evaled').html(v);
  }
}

function ExpLayoutView() {
  this.controller = arguments[0];
  this.model = arguments[1];
  this.children = [];
  this.elmt = null;
  
  this.toHtmlString = function() { return this.model.toHtmlString() }
  
  this.toElmt = function() {
    var elmt;
    
    switch (this.model.type) {
    case 'CASE':
      var branches = this.model.branches;
      
      elmt = document.createElement('div');
      $(elmt).append(this.cond.toLayout());
      for (var i = 0; i < branches.length; i += 2) {
        // Make a div of each branch
        var div = document.createElement('div');
        $(div).append(branches[i].toLayout());
        if (i != branches.length - 1) {
          $(div).append(branches[i+1].toLayout());
        }
        // Set the class
        div.className = 'case_branch';

        $(elmt).append(div);
      }

      var div = document.createElement('div');
      $(div).append(this.toHtmlString());
      if (this.evaled) {
        $(div).append('<span class="evaled">' + this.evaled + '</span>');
      }
      div.className = 'label';
      $(elmt).append(div);
      elmt.className = this.className;
      break;
    
    default:
      elmt = document.createElement('div');
      $.each(this.children, function(i, childView) {
        if (childView.length) {
          $.each(childView, function(j, subchildView) {
            $(elmt).append(subchildView.toLayout());
          });
        }
        else {
          $(elmt).append(childView.toLayout());
        }
      });
      var div = document.createElement('div');
      $(div).append(this.toHtmlString());
      if (this.evaled) {
        $(div).append('<span class="evaled">' + this.evaled + '</span>');
      }
      $(elmt).append(div);
      elmt.className = this.model.className;
      break;
    }
    
    this.elmt = elmt;
    return elmt;
  }
  
  this.updateEvaled = function(v) {
    this.evaled = v;
    $(elmt).find('.evaled').html(v);
  }
}

function createView(controller, e, viewConstructor) {
  var view = new viewConstructor(controller, e);
  e.meta.views.push(view);
  
  $.each(e.getChildren(), function(i, eChild) {
    if (eChild.constructor == Array) {
      $.each(eChild, function(j, eSubChild) {
        view.children.push(createView(controller, eSubChild, viewConstructor));
      });
    }
    else {
      view.children.push(createView(controller, eChild, viewConstructor));
    }
  });
  
  return view;
}

// Returns true iff e is a value.
function isValue(e) {
  switch(e.type) {
  case 'INT':
  case 'NIL':
  case 'PAIR':
  case 'PRIM':
  case 'CLOSURE':
    return true;
  default:
    return false;
  }
}

// TODO: implement.  Right now force still (incorrectly) returns things like
// pairs of channels.
function isNormalForm(e) {
  return isValue(e);
}

// Returns true iff e is in weak head normal form (WHNF).
// Basically, this is a fancy way of saying that the caller needs to force
// evaluation of e enough so that it can see its top-level form or shape.  In
// this language an exp is in WHNF if it is not immediately reducable.
function isWhnf(e) {
  switch(e.type) {
  case 'INT':
  case 'NIL':
  case 'PAIR':
  case 'PRIM':
  case 'CLOSURE':
    return true;
  default:
    return false;
  }
}

// Returns true iff eCond matches the pattern.
function matches(ctx, ePattern, eCond) {
  switch (ePattern.type) {
  case 'PAIR':
    return ePattern.type == eCond.type &&
           matches(ePattern.first,  eCond.first) &&
           matches(ePattern.second, eCond.second);
  case 'NIL':
    return ePattern.type == eCond.type;
  case 'INT':
    return ePattern.type == eCond.type &&
           ePattern.intVal == eCond.intVal;
  case 'SYM':
    // Symbols match anything.  ???
    return true;
  case 'PRIM':
    return ePattern.type == eCond.type &&
           ePattern.primOp == eCond.primOp;
  default:
    console.error('Invalid pattern of type: ' + ePattern.type);
    throw ePattern;
  }
}

// Evaluates e in the given context.
// This always returns immediately, possibly spawning a new thread/channel.
function eval(ctx, e) {
  // If e is a value, don't spawn.
  if (isValue(e)) return e;
  
  // If e is already a channel, don't spawn.
  if (e.type == 'CHAN') {
    // If the channel has already been sent a value, remove the channel.
    if (e.value)  dbg('popping chan %o with value %s', e, e.value);
    if (!e.value) dbg('evaling chan %s', e);
    return (e.value) ? e.value
                     : e
  }
  
  var ch = new Exp('CHAN', e.meta, ctx, e);
  
  // Wrap call to evalStep so that we can return immediately and
  // send the eventual return value to the channel.
  var g = function() {
    var v = evalStep(ch.ctx, ch.sender);
    
    // Cache results
    if (v !== ch.sender) {
      ch.sender.evaled = v;
      ch.sender.updateEvaled(v);
    }
    
    // Channel determines whether we should be removed from the queue.
    return ch.send(v);
  }
  
  // Add g to the global thread queue.
  dbg('pushing ', e, ch);
  addToWorkQueue({thunk: g, chan: ch});
  
  return ch;
}

// Evaluate e in the given context.
// This only takes one step of evaluation, so the returned exp may not be
// in normal form.
function evalStep(ctx, e) {
  switch (e.type) {
  case 'NIL':
    return e;
  case 'PAIR':
    return e;
  case 'FST':
    var p = eval(ctx, e.pair);
    return (p.type == 'PAIR') ? p.first
                              : new Exp('FST', e.meta, p);
  case 'SND':
    var p = eval(ctx, e.pair);
    return (p.type == 'PAIR') ? p.second
                              : new Exp('SND', e.meta, p);
  case 'INT':
    return e;
  case 'SYM':
    dbg('cloning', e.symVal);
    return clone(ctx[e.symVal]);
  case 'PRIM':
    return e;
  case 'FUN':
    return new Exp('CLOSURE', e.meta, ctx, e.params, e.body, e.fixPoint);
  case 'CLOSURE':
    return e;
  case 'CHAN':
    return (e.value) ? e.value
                     : e;
  case 'APP':
    var f = eval(ctx, e.fun);
    var args = $.map(e.args, function(e) {
            return eval(ctx, e);
          });
    
    if (f.type == 'PRIM') {
      var notAllInt = function() {
        for (var i = 0; i < args.length; i++) {
          if (args[i].type != 'INT') return true;
        }
        return false;
      }
      
      switch (f.primOp) {
      case 'ADD':
        if (notAllInt()) return new Exp('APP', e.meta, f, args);
        s = 0;
        $.each(args, function() {
          s += this.intVal;
        });
        return new Exp('INT', e.meta, s);
      case 'MUL':
        if (notAllInt()) return new Exp('APP', e.meta, f, args);
        s = 1;
        $.each(args, function() {
          s *= this.intVal;
        });
        return new Exp('INT', e.meta, s);
      case 'SUB':
        if (notAllInt()) return new Exp('APP', e.meta, f, args);
        return new Exp('INT', e.meta, args[0].intVal - args[1].intVal);
      case 'NEG':
        if (notAllInt()) return new Exp('APP', e.meta, f, args);
        return new Exp('INT', e.meta, -args[0].intVal);
      case '=':
        // TODO: Fix this
        if (args[0].eq(args[1])) {
          return new Exp('INT', e.meta, 1);
        }
        else {
          return new Exp('NIL', e.meta);
        }
      default:
        console.error('Unknown primitive op: ', f);
        throw e;
      }
    }
    else if (f.type == 'CLOSURE') {
      if (args.length > f.params.length) {
        console.error('Function expects %d parameter(s); applied to %d args', f.params.length, args.length);
        throw e;
      }

      // Clone the context so we leave the original in tact.
      appCtx = clone(f.ctx);
      // Bind fix point
      if (f.fixPoint) {
        appCtx[f.fixPoint] = f;
      }
      // Bind arguments to params
      $.each(args, function(i, arg) {
        appCtx[f.params[i].symVal] = arg;
      });
      // Eval in the new context
      var v = eval(appCtx, f.body);

      return v;
    }
    return new Exp('APP', e.meta, f, args);
    
  case 'CASE':
    var vCond = eval(ctx, e.cond);
    
    if (!isWhnf(vCond)) return new Exp('CASE', e.meta, vCond, e.branches);
    
    for (var i = 0; i < e.branches.length; i += 2) {
      // If we've reached the end, the last pattern is actually the else
      // branch.
      if (i == e.branches.length - 1) {
        return eval(ctx, e.branches[i]);
      }

      // If pattern matches, evaluate the branch
      if (matches(ctx, e.branches[i], vCond)) {
        return eval(ctx, e.branches[i+1]);
      }
    }
    console.error('Malformed case expression; missing else branch', e);
    throw e;
    
  default:
    console.error('Can not evalate expression of unknown type: %s', e.type, e);
  }
}

// Force evaluation of e in the given context.
// This calls evalStep repeatedly until e is in normal form.
// A callback can optionally be given to watch evaluation step by step.
function force(ctx, e) {
  var t = 0;
  var callback = (arguments.length > 2) ? arguments[2] : null;
  
  while (!isNormalForm(e)) {
    // step each thing in the queue
    newQ = $.grep(q, function(work) {
      var keep = ! work.thunk();  // do work
      if (callback) callback(e, t);
      return keep;
    });
    q = newQ.concat(pushedToQ);
    pushedToQ = [];
    
    var e2 = evalStep(ctx, e);
    e = e2;
    
    // Show the caller where we are so far.
    if (callback) callback(e, t);
    
    // Track how many steps we've taken.
    t++;
    
    // Exit early if we've been running a long time.
    if (window.debug && t >= 100) {
      dbg('q', q);
      console.error('force took too many iterations (%d). Turn off window.debug to continue unbounded.', t);
      return e;
    }
  }
  
  console.info('force iterations:', t);
  return e;
}

// The empty context used for evaluation.
function emptyCtx() {
  return {};
}
