using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Data;
using System.Windows.Documents;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Imaging;
using System.Windows.Shapes;

namespace PageExtractor
{
    /// <summary>
    /// PropertyWindow.xaml 的交互逻辑
    /// </summary>
    public partial class PropertyWindow : Window
    {
        private int _maxDepth;
        private int _maxConnection;

        public int MaxDepth
        {
            get
            {
                return _maxDepth;
            }
            set
            {
                _maxDepth = value;
            }
        }

        public int MaxConnection
        {
            get
            {
                return _maxConnection;
            }
            set
            {
                _maxConnection = value;
                
            }
        }


        public PropertyWindow()
        {
            InitializeComponent();
            WindowStartupLocation = System.Windows.WindowStartupLocation.CenterScreen;
            Loaded += new RoutedEventHandler(PropertyWindow_Loaded);
        }

        void PropertyWindow_Loaded(object sender, RoutedEventArgs e)
        {
            TextMaxConnection.Text = _maxConnection.ToString();
            TextMaxDepth.Text = _maxDepth.ToString();
        }

        private void OkButton_Click(object sender, RoutedEventArgs e)
        {
            _maxDepth = int.Parse(TextMaxDepth.Text.Trim());
            _maxConnection = int.Parse(TextMaxConnection.Text.Trim());
            this.DialogResult = true;
            Close();
        }

        private void CancelButton_Click(object sender, RoutedEventArgs e)
        {
            this.DialogResult = false;
            Close();
        }
    }
}
