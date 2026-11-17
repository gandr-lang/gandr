// The search of a `gandr doc` site. `search.js` sets `window.gandrItems`,
// one row per item: its name, its kind, its page and its summary. A query
// lists the items whose name holds it first, then the items whose summary
// holds it, at most fifty.
(function () {
  "use strict";
  var input = document.getElementById("search");
  var list = document.getElementById("results");
  var root = document.body.dataset.root || "";
  var items = window.gandrItems || [];
  var limit = 50;

  function row(item) {
    var entry = document.createElement("li");
    var link = document.createElement("a");
    var name = document.createElement("code");
    link.href = root + item[2];
    name.textContent = item[0];
    link.appendChild(name);
    entry.appendChild(link);
    entry.appendChild(document.createTextNode(" " + item[1] + (item[3] ? " — " + item[3] : "")));
    return entry;
  }

  function search() {
    var query = input.value.trim().toLowerCase();
    list.textContent = "";
    if (!query) {
      return;
    }
    var named = [];
    var described = [];
    for (var i = 0; i < items.length; i++) {
      if (items[i][0].toLowerCase().indexOf(query) >= 0) {
        named.push(items[i]);
      } else if (items[i][3].toLowerCase().indexOf(query) >= 0) {
        described.push(items[i]);
      }
    }
    named.concat(described).slice(0, limit).forEach(function (item) {
      list.appendChild(row(item));
    });
  }

  input.addEventListener("input", search);
  input.addEventListener("keydown", function (event) {
    if (event.key === "Escape") {
      input.value = "";
      search();
    }
  });
})();
